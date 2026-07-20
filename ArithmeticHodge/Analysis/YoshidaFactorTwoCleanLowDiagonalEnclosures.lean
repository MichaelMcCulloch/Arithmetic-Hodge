import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaDiagonalHigherAcceleration
import ArithmeticHodge.Analysis.YoshidaEulerGammaUltraFine
import ArithmeticHodge.Analysis.YoshidaEvenZeroMomentEnclosure
import ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead
import ArithmeticHodge.Analysis.YoshidaZeroModeStieltjesIdentity
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false
set_option maxRecDepth 100000

open scoped BigOperators
open Filter

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCleanLowDiagonalEnclosures

noncomputable section

open RatInterval
open YoshidaDiagonalAcceleratedSeries
open YoshidaDiagonalHigherAcceleration
open YoshidaDiagonalMomentEnclosures
open YoshidaDiagonalSeriesTail
open YoshidaEulerGammaUltraFine
open YoshidaEvenZeroMomentEnclosure
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures
open YoshidaSineCheckpointedHead
open YoshidaZeroModeStieltjesIdentity
open YoshidaZeroModeStructuralCore

/-!
# Clean low-frequency diagonal enclosures

The accelerated diagonal series is evaluated with a common ultra-fine base
and kernel-checked rational finite heads.  Mode zero uses its separately
proved accelerated identity and also retains the structural Stieltjes closed
form.
-/

private def lowLogTwoInterval : RatInterval :=
  factorTwoPrimeLogTwoInterval

private theorem lowLogTwoInterval_contains :
    lowLogTwoInterval.Contains yoshidaLength := by
  have h := factorTwoPrimeLogTwoInterval_contains
  unfold YoshidaFactorTwoPhasePerturbationMomentSeries.factorTwoMomentLength
    YoshidaEndpointHyperbolicBound.yoshidaEndpointA at h
  unfold lowLogTwoInterval
  convert h using 1
  all_goals unfold YoshidaOddGramPrefix.yoshidaLength
  all_goals ring

private def logRatioLower (x : ℚ) : ℚ :=
  2 * ∑ i ∈ Finset.range 24, x ^ (2 * i + 1) / (2 * i + 1)

private def logRatioUpper (x : ℚ) : ℚ :=
  logRatioLower x + 2 * x ^ 49 / (1 - x ^ 2)

private def logRatioInterval (x : ℚ) : RatInterval :=
  ⟨logRatioLower x, logRatioUpper x⟩

private theorem logRatioInterval_contains
    {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (logRatioInterval x).Contains
      (Real.log ((((1 + x) / (1 - x) : ℚ) : ℝ))) := by
  have hx0R : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1R : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hlo := Real.sum_range_le_log_div hx0R hx1R 24
  have hup := Real.log_div_le_sum_range_add hx0R hx1R 24
  constructor
  · change ((logRatioLower x : ℚ) : ℝ) ≤ _
    unfold logRatioLower
    push_cast
    norm_num only at hlo ⊢
    linarith
  · change _ ≤ ((logRatioUpper x : ℚ) : ℝ)
    unfold logRatioUpper logRatioLower
    push_cast
    norm_num only at hup ⊢
    calc
      Real.log ((1 + (x : ℝ)) / (1 - (x : ℝ))) =
          2 * (1 / 2 * Real.log ((1 + (x : ℝ)) / (1 - (x : ℝ)))) := by
        ring
      _ ≤ 2 * ((∑ i ∈ Finset.range 24,
          (x : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
          (x : ℝ) ^ 49 / (1 - (x : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hup (by norm_num)
      _ = _ := by ring

private def lowLogPiXLower : ℚ :=
  (piFineInterval.lower - 1) / (piFineInterval.lower + 1)

private def lowLogPiXUpper : ℚ :=
  (piFineInterval.upper - 1) / (piFineInterval.upper + 1)

private def lowLogPiInterval : RatInterval :=
  ⟨logRatioLower lowLogPiXLower, logRatioUpper lowLogPiXUpper⟩

private theorem lowLogPiInterval_contains :
    lowLogPiInterval.Contains (Real.log Real.pi) := by
  have hxLower0 : 0 ≤ lowLogPiXLower := by
    norm_num [lowLogPiXLower, piFineInterval]
  have hxLower1 : lowLogPiXLower < 1 := by
    norm_num [lowLogPiXLower, piFineInterval]
  have hxUpper0 : 0 ≤ lowLogPiXUpper := by
    norm_num [lowLogPiXUpper, piFineInterval]
  have hxUpper1 : lowLogPiXUpper < 1 := by
    norm_num [lowLogPiXUpper, piFineInterval]
  have hlo := (logRatioInterval_contains hxLower0 hxLower1).1
  have hup := (logRatioInterval_contains hxUpper0 hxUpper1).2
  have hratioLower :
      (((1 + lowLogPiXLower) / (1 - lowLogPiXLower) : ℚ) : ℝ) =
        (piFineInterval.lower : ℚ) := by
    norm_num [lowLogPiXLower, piFineInterval]
  have hratioUpper :
      (((1 + lowLogPiXUpper) / (1 - lowLogPiXUpper) : ℚ) : ℝ) =
        (piFineInterval.upper : ℚ) := by
    norm_num [lowLogPiXUpper, piFineInterval]
  rw [hratioLower] at hlo
  rw [hratioUpper] at hup
  have hpiLower : (piFineInterval.lower : ℝ) < Real.pi := by
    have h := Real.pi_gt_d20
    norm_num [piFineInterval] at h ⊢
    exact h
  have hpiUpper : Real.pi < (piFineInterval.upper : ℝ) := by
    have h := Real.pi_lt_d20
    norm_num [piFineInterval] at h ⊢
    exact h
  unfold lowLogPiInterval
  constructor
  · simpa only [logRatioInterval] using
      hlo.trans (Real.log_lt_log (by norm_num [piFineInterval]) hpiLower).le
  · simpa only [logRatioInterval] using
      (Real.log_lt_log Real.pi_pos hpiUpper).le.trans hup

private def lowLogFourThirdsInterval : RatInterval :=
  logRatioInterval (1 / 7)

private theorem lowLogFourThirdsInterval_contains :
    lowLogFourThirdsInterval.Contains (Real.log (4 / 3)) := by
  have h := logRatioInterval_contains
    (x := (1 / 7 : ℚ)) (by norm_num) (by norm_num)
  norm_num only at h
  exact h

private def lowYInterval (n : ℕ) : RatInterval :=
  ⟨piFineInterval.lower * n / lowLogTwoInterval.upper,
    piFineInterval.upper * n / lowLogTwoInterval.lower⟩

private theorem lowYInterval_contains (n : ℕ) :
    (lowYInterval n).Contains (Real.pi * n / yoshidaLength) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnum0 : 0 ≤ Real.pi * (n : ℝ) :=
    mul_nonneg Real.pi_pos.le hn0
  have hnumLo : (piFineInterval.lower : ℝ) * (n : ℝ) ≤
      Real.pi * (n : ℝ) :=
    mul_le_mul_of_nonneg_right piFineInterval_contains.1 hn0
  have hnumHi : Real.pi * (n : ℝ) ≤
      (piFineInterval.upper : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right piFineInterval_contains.2 hn0
  have hLlo : (0 : ℝ) < (lowLogTwoInterval.lower : ℚ) := by
    norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval]
  unfold lowYInterval
  constructor
  · norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    exact div_le_div₀ hnum0 hnumLo yoshidaLength_pos
      lowLogTwoInterval_contains.2
  · norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    exact div_le_div₀
      (mul_nonneg (by norm_num [piFineInterval]) hn0) hnumHi hLlo
      lowLogTwoInterval_contains.1

private theorem lowYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (lowYInterval n).lower := by
  unfold lowYInterval lowLogTwoInterval factorTwoPrimeLogTwoInterval
    piFineInterval
  positivity

private def lowPositiveSquare (I : RatInterval) : RatInterval :=
  ⟨I.lower ^ 2, I.upper ^ 2⟩

private theorem lowPositiveSquare_contains
    {I : RatInterval} {x : ℝ} (hI0 : 0 ≤ I.lower)
    (hx : I.Contains x) :
    (lowPositiveSquare I).Contains (x ^ 2) := by
  unfold Contains at hx
  unfold lowPositiveSquare Contains
  norm_num only [Rat.cast_pow]
  constructor
  · exact pow_le_pow_left₀ (by exact_mod_cast hI0) hx.1 2
  · exact pow_le_pow_left₀ (by
      exact (show (0 : ℝ) ≤ (I.lower : ℚ) by exact_mod_cast hI0).trans hx.1)
      hx.2 2

private def lowKappaSqInterval (n : ℕ) : RatInterval :=
  pure 4 * lowPositiveSquare (lowYInterval n)

private theorem lowKappaSqInterval_contains (n : ℕ) :
    (lowKappaSqInterval n).Contains (yoshidaKappa n ^ 2) := by
  have hy := lowYInterval_contains n
  have hySq := lowPositiveSquare_contains (lowYInterval_lower_nonneg n) hy
  have h := contains_mul (contains_pure 4) hySq
  unfold lowKappaSqInterval yoshidaKappa
  convert h using 1
  ring

private theorem lowKappaSqInterval_lower_nonneg (n : ℕ) :
    0 ≤ (lowKappaSqInterval n).lower := by
  unfold lowKappaSqInterval lowPositiveSquare lowYInterval
  change 0 ≤ min
    (min (4 * (piFineInterval.lower * n / lowLogTwoInterval.upper) ^ 2)
      (4 * (piFineInterval.upper * n / lowLogTwoInterval.lower) ^ 2))
    (min (4 * (piFineInterval.lower * n / lowLogTwoInterval.upper) ^ 2)
      (4 * (piFineInterval.upper * n / lowLogTwoInterval.lower) ^ 2))
  simp only [min_self, le_min_iff]
  constructor <;> positivity

private theorem mul_lower_pos_of_pos
    {I J : RatInterval}
    (hI : 0 < I.lower) (hJ : 0 < J.lower)
    (hIv : I.Valid) (hJv : J.Valid) :
    0 < (I * J).lower := by
  have hIu : 0 < I.upper := hI.trans_le hIv
  have hJu : 0 < J.upper := hJ.trans_le hJv
  change 0 < min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper))
  simp only [lt_min_iff]
  exact ⟨⟨mul_pos hI hJ, mul_pos hI hJu⟩,
    ⟨mul_pos hIu hJ, mul_pos hIu hJu⟩⟩

private def lowDiagonalRampInterval
    (n : ℕ) (a : ℚ) (q : RatInterval) : RatInterval :=
  let L := lowLogTwoInterval
  let p := lowKappaSqInterval n
  let aI := pure a
  let aSq := pure (a ^ 2)
  ((q - pure 1 + aI * L) * (aSq - p) +
      pure 2 * aI * p * L) /
    (L * lowPositiveSquare (aSq + p))

private theorem lowDiagonalRampInterval_contains
    (n : ℕ) (a : ℚ) (q : RatInterval) {z : ℝ}
    (ha : a ≠ 0) (hq : q.Contains z) :
    (lowDiagonalRampInterval n a q).Contains
      (diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2) (a : ℝ) z) := by
  let L := lowLogTwoInterval
  let p := lowKappaSqInterval n
  let aI := pure a
  let aSq := pure (a ^ 2)
  have hL : L.Contains yoshidaLength := lowLogTwoInterval_contains
  have hp : p.Contains (yoshidaKappa n ^ 2) := lowKappaSqInterval_contains n
  have haI : aI.Contains (a : ℝ) := contains_pure a
  have haSq : aSq.Contains ((a : ℝ) ^ 2) := by
    constructor <;> norm_num [aSq, Contains, RatInterval.pure]
  have hsum : (aSq + p).Contains ((a : ℝ) ^ 2 + yoshidaKappa n ^ 2) :=
    contains_add haSq hp
  have hsumLower : 0 < (aSq + p).lower := by
    change 0 < a ^ 2 + p.lower
    exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha)
      (by simpa only [p] using lowKappaSqInterval_lower_nonneg n)
  have hsq : (lowPositiveSquare (aSq + p)).Contains
      (((a : ℝ) ^ 2 + yoshidaKappa n ^ 2) ^ 2) :=
    lowPositiveSquare_contains hsumLower.le hsum
  have hden := contains_mul hL hsq
  have hdenLower : 0 < (L * lowPositiveSquare (aSq + p)).lower := by
    apply mul_lower_pos_of_pos
    · norm_num [L, lowLogTwoInterval, factorTwoPrimeLogTwoInterval]
    · unfold lowPositiveSquare
      exact sq_pos_of_pos hsumLower
    · exact valid_of_contains hL
    · exact valid_of_contains hsq
  have hnum := contains_add
    (contains_mul
      (contains_add (contains_sub hq (contains_pure 1))
        (contains_mul haI hL))
      (contains_sub haSq hp))
    (contains_mul (contains_mul (contains_mul (contains_pure 2) haI) hp) hL)
  unfold lowDiagonalRampInterval diagonalRampClosed
  dsimp only
  exact contains_div_of_pos hdenLower (by
    convert hnum using 1
    all_goals ring) hden

private def lowDiagonalAInterval : RatInterval :=
  pure 1 / (pure 2 * lowLogTwoInterval) + pure (1 / 4)

private theorem lowDiagonalAInterval_contains :
    lowDiagonalAInterval.Contains diagonalAValue := by
  have hden := contains_mul (contains_pure 2) lowLogTwoInterval_contains
  have hone : (RatInterval.pure (1 : ℚ)).Contains (1 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hquarter : (RatInterval.pure (1 / 4 : ℚ)).Contains (1 / 4 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hdenLower : 0 < (pure 2 * lowLogTwoInterval).lower := by
    apply mul_lower_pos_of_pos
    · norm_num [RatInterval.pure]
    · norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval]
    · exact valid_of_contains (contains_pure 2)
    · exact valid_of_contains lowLogTwoInterval_contains
  unfold lowDiagonalAInterval diagonalAValue
  exact contains_add
    (contains_div_of_pos hdenLower hone hden)
    hquarter

private def lowDiagonalBaseInterval (n : ℕ) : RatInterval :=
  pure 2 * lowDiagonalRampInterval n (-1 / 2) sqrtTwoInterval -
      eulerGammaUltraFineInterval - lowLogPiInterval +
    lowLogFourThirdsInterval +
      lowDiagonalAInterval * positiveSquare piFineInterval / pure 6

private theorem lowDiagonalBaseInterval_contains (n : ℕ) :
    (lowDiagonalBaseInterval n).Contains (diagonalAcceleratedBase n) := by
  rw [← diagonalBaseValue_eq_acceleratedBase]
  have hramp := lowDiagonalRampInterval_contains n (-1 / 2) sqrtTwoInterval
    (by norm_num) sqrtTwoInterval_contains
  have hramp' : (lowDiagonalRampInterval n (-1 / 2) sqrtTwoInterval).Contains
      (diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
        (-1 / 2 : ℝ) (Real.sqrt 2)) := by
    convert hramp using 1
    norm_num
  have hpiSq : (positiveSquare piFineInterval).Contains (Real.pi ^ 2) :=
    positiveSquare_contains (by norm_num [piFineInterval])
      piFineInterval_contains
  have htail := contains_div_of_pos (by norm_num [RatInterval.pure])
    (contains_mul lowDiagonalAInterval_contains hpiSq) (contains_pure 6)
  unfold lowDiagonalBaseInterval diagonalBaseValue
  exact contains_add
    (contains_add
      (contains_sub
        (contains_sub (contains_mul (contains_pure 2) hramp')
          eulerGammaUltraFineInterval_contains)
        lowLogPiInterval_contains)
      lowLogFourThirdsInterval_contains)
    htail

private def lowDiagonalCorrectionInterval (n k : ℕ) : RatInterval :=
  let kQ : ℚ := k
  pure 2 * lowDiagonalRampInterval n (2 * kQ + 1 / 2)
      (sqrtDyadicInterval k) -
    (pure 1 - dyadicInterval k) / pure kQ +
      lowDiagonalAInterval / pure (kQ ^ 2)

private theorem lowDiagonalCorrectionInterval_contains
    (n k : ℕ) (hk : 0 < k) :
    (lowDiagonalCorrectionInterval n k).Contains
      (yoshidaDiagonalDyadicPairedCorrection n k) := by
  let kQ : ℚ := k
  let aQ : ℚ := 2 * kQ + 1 / 2
  have haQ : aQ ≠ 0 := by
    dsimp [aQ, kQ]
    positivity
  have hramp := lowDiagonalRampInterval_contains n aQ
    (sqrtDyadicInterval k) haQ (sqrtDyadicInterval_contains k)
  have hramp' :
      (lowDiagonalRampInterval n aQ (sqrtDyadicInterval k)).Contains
        (diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
          (2 * (k : ℝ) + 1 / 2)
          ((Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k)) := by
    convert hramp using 1
    norm_num [aQ, kQ]
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hone : (RatInterval.pure (1 : ℚ)).Contains (1 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hkI : (RatInterval.pure kQ).Contains (k : ℝ) := by
    simpa only [kQ] using contains_pure kQ
  have hkSqI : (RatInterval.pure (kQ ^ 2)).Contains ((k : ℝ) ^ 2) := by
    constructor <;> norm_num [Contains, RatInterval.pure, kQ]
  have hquot := contains_div_of_pos (by
      change 0 < kQ
      dsimp [kQ]
      exact_mod_cast hk)
    (contains_sub hone (dyadicInterval_contains k)) hkI
  have hAquot := contains_div_of_pos (by
      change 0 < kQ ^ 2
      dsimp [kQ]
      positivity)
    lowDiagonalAInterval_contains hkSqI
  have h := contains_add
    (contains_sub (contains_mul htwo hramp') hquot) hAquot
  unfold lowDiagonalCorrectionInterval
    yoshidaDiagonalDyadicPairedCorrection diagonalDyadicPairedCorrection
    diagonalPairedCorrection
  dsimp only
  simpa only [kQ, aQ, diagonalAValue] using h

private noncomputable def lowDiagonalHeadValueAux
    (n : ℕ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | fuel + 1, k =>
      yoshidaDiagonalDyadicPairedCorrection n k +
        lowDiagonalHeadValueAux n fuel (k + 1)

private def lowDiagonalHeadIntervalAux
    (n : ℕ) : ℕ → ℕ → RatInterval → RatInterval
  | 0, _, acc => acc
  | fuel + 1, k, acc =>
      lowDiagonalHeadIntervalAux n fuel (k + 1)
        (acc + lowDiagonalCorrectionInterval n k)

private def lowDiagonalHeadInterval (n K : ℕ) : RatInterval :=
  lowDiagonalHeadIntervalAux n K 1 (pure 0)

private theorem lowDiagonalHeadIntervalAux_contains
    (n fuel k : ℕ) (hk : 0 < k) (acc : RatInterval) (x : ℝ)
    (hx : acc.Contains x) :
    (lowDiagonalHeadIntervalAux n fuel k acc).Contains
      (x + lowDiagonalHeadValueAux n fuel k) := by
  induction fuel generalizing k acc x with
  | zero =>
      simpa [lowDiagonalHeadIntervalAux, lowDiagonalHeadValueAux] using hx
  | succ fuel ih =>
      rw [lowDiagonalHeadIntervalAux, lowDiagonalHeadValueAux]
      have hacc := contains_add hx (lowDiagonalCorrectionInterval_contains n k hk)
      have hrec := ih (k + 1) (by omega)
        (acc + lowDiagonalCorrectionInterval n k)
        (x + yoshidaDiagonalDyadicPairedCorrection n k) hacc
      convert hrec using 1
      ring

private theorem lowDiagonalHeadValueAux_eq_sum (n fuel k : ℕ) :
    lowDiagonalHeadValueAux n fuel k =
      ∑ j ∈ Finset.range fuel,
        yoshidaDiagonalDyadicPairedCorrection n (k + j) := by
  induction fuel generalizing k with
  | zero => simp [lowDiagonalHeadValueAux]
  | succ fuel ih =>
      rw [lowDiagonalHeadValueAux, Finset.sum_range_succ']
      rw [ih]
      have hshift :
          (∑ j ∈ Finset.range fuel,
              yoshidaDiagonalDyadicPairedCorrection n ((k + 1) + j)) =
            ∑ j ∈ Finset.range fuel,
              yoshidaDiagonalDyadicPairedCorrection n (k + (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact congrArg (yoshidaDiagonalDyadicPairedCorrection n) (by omega)
      rw [hshift]
      simp only [Nat.add_zero]
      ring

private theorem lowDiagonalHeadInterval_contains (n K : ℕ) :
    (lowDiagonalHeadInterval n K).Contains
      (∑ j ∈ Finset.range K,
        yoshidaDiagonalDyadicPairedCorrection n (1 + j)) := by
  have hzero : (RatInterval.pure (0 : ℚ)).Contains (0 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have h := lowDiagonalHeadIntervalAux_contains n K 1 (by norm_num)
    (RatInterval.pure 0) 0 hzero
  rw [lowDiagonalHeadValueAux_eq_sum] at h
  simpa only [lowDiagonalHeadInterval, zero_add] using h

private def lowDiagonalChunkInterval (n start len : ℕ) : RatInterval :=
  lowDiagonalHeadIntervalAux n len start (pure 0)

private theorem lowDiagonalHeadIntervalAux_acc
    (n fuel k : ℕ) (acc : RatInterval) :
    lowDiagonalHeadIntervalAux n fuel k acc =
      acc + lowDiagonalHeadIntervalAux n fuel k (pure 0) := by
  induction fuel generalizing k acc with
  | zero => simp [lowDiagonalHeadIntervalAux, add_pure_zero]
  | succ fuel ih =>
      simp only [lowDiagonalHeadIntervalAux]
      rw [ih (k := k + 1) (acc := acc + lowDiagonalCorrectionInterval n k)]
      rw [ih (k := k + 1)
        (acc := pure 0 + lowDiagonalCorrectionInterval n k)]
      rw [pure_zero_add, interval_add_assoc]

private theorem lowDiagonalHeadIntervalAux_add
    (n a b k : ℕ) (acc : RatInterval) :
    lowDiagonalHeadIntervalAux n (a + b) k acc =
      lowDiagonalHeadIntervalAux n b (k + a)
        (lowDiagonalHeadIntervalAux n a k acc) := by
  induction a generalizing k acc with
  | zero => simp [lowDiagonalHeadIntervalAux]
  | succ a ih =>
      rw [Nat.succ_add]
      simp only [lowDiagonalHeadIntervalAux]
      rw [ih]
      congr 1
      omega

private def lowFullChunkedHead (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | chunks + 1 =>
      lowFullChunkedHead n chunks +
        lowDiagonalChunkInterval n (1 + 256 * chunks) 256

private theorem lowFullChunkedHead_eq (n chunks : ℕ) :
    lowFullChunkedHead n chunks =
      lowDiagonalHeadIntervalAux n (256 * chunks) 1 (pure 0) := by
  induction chunks with
  | zero => rfl
  | succ chunks ih =>
      rw [lowFullChunkedHead, ih]
      rw [show 256 * (chunks + 1) = 256 * chunks + 256 by omega]
      rw [lowDiagonalHeadIntervalAux_add]
      rw [lowDiagonalHeadIntervalAux_acc n 256 (1 + 256 * chunks)
        (lowDiagonalHeadIntervalAux n (256 * chunks) 1 (pure 0))]
      simp only [lowDiagonalChunkInterval]

private def lowScheduledChunkLength (total i : ℕ) : ℕ :=
  if i + 1 = total then 255 else 256

private def lowScheduledChunkInterval (n total i : ℕ) : RatInterval :=
  lowDiagonalChunkInterval n (1 + 256 * i)
    (lowScheduledChunkLength total i)

private def lowExactCheckpointHead (n total : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | used + 1 =>
      lowExactCheckpointHead n total used +
        lowScheduledChunkInterval n total used

private theorem lowExactCheckpointHead_eq_full_of_lt
    (n total used : ℕ) (hused : used < total) :
    lowExactCheckpointHead n total used = lowFullChunkedHead n used := by
  induction used with
  | zero => rfl
  | succ used ih =>
      rw [lowExactCheckpointHead, lowFullChunkedHead]
      rw [ih (by omega)]
      unfold lowScheduledChunkInterval lowScheduledChunkLength
      rw [if_neg (by omega)]

private theorem lowExactCheckpointHead_eq_diagonalHead
    (n chunks : ℕ) (hchunks : 0 < chunks) :
    lowExactCheckpointHead n chunks chunks =
      lowDiagonalHeadInterval n (256 * chunks - 1) := by
  cases chunks with
  | zero => omega
  | succ chunks =>
      rw [lowExactCheckpointHead]
      rw [lowExactCheckpointHead_eq_full_of_lt n (chunks + 1) chunks (by omega)]
      rw [lowFullChunkedHead_eq]
      rw [lowDiagonalHeadInterval,
        show 256 * (chunks + 1) - 1 = 256 * chunks + 255 by omega]
      rw [lowDiagonalHeadIntervalAux_add]
      rw [lowDiagonalHeadIntervalAux_acc n 255 (1 + 256 * chunks)
        (lowDiagonalHeadIntervalAux n (256 * chunks) 1 (pure 0))]
      simp only [lowScheduledChunkInterval, lowScheduledChunkLength,
        lowDiagonalChunkInterval, if_true]

private def lowRoundedChunkBox
    (n total : ℕ) (scale : ℚ) (i : ℕ) : RatInterval :=
  YoshidaSineCheckpointedHead.outwardRoundedInterval scale
    (lowScheduledChunkInterval n total i)

private theorem lowScheduledChunkInterval_sub_rounded
    (n total i : ℕ) {scale : ℚ} (hscale : 0 < scale) :
    IsSubinterval (lowScheduledChunkInterval n total i)
      (lowRoundedChunkBox n total scale i) :=
  YoshidaSineCheckpointedHead.outwardRoundedInterval_subinterval hscale _

private theorem lowCheckpointHead_subinterval
    (n chunks : ℕ) (box : ℕ → RatInterval)
    (hcert : ∀ i, i < chunks →
      IsSubinterval (lowScheduledChunkInterval n chunks i) (box i)) :
    IsSubinterval (lowExactCheckpointHead n chunks chunks)
      (coarseCheckpointHead box chunks) := by
  have hprefix : ∀ used, used ≤ chunks →
      IsSubinterval (lowExactCheckpointHead n chunks used)
        (coarseCheckpointHead box used) := by
    intro used hused
    induction used with
    | zero => exact isSubinterval_refl _
    | succ used ih =>
        rw [lowExactCheckpointHead, coarseCheckpointHead]
        exact isSubinterval_add (ih (by omega)) (hcert used (by omega))
  exact hprefix chunks le_rfl

private theorem lowDiagonalHeadInterval_sub_rounded
    (n chunks : ℕ) (hchunks : 0 < chunks) {scale : ℚ}
    (hscale : 0 < scale) :
    IsSubinterval (lowDiagonalHeadInterval n (256 * chunks - 1))
      (coarseCheckpointHead (lowRoundedChunkBox n chunks scale) chunks) := by
  rw [← lowExactCheckpointHead_eq_diagonalHead n chunks hchunks]
  exact lowCheckpointHead_subinterval n chunks _
    (fun i _ ↦ lowScheduledChunkInterval_sub_rounded n chunks i hscale)

private def lowCoreCoeffThreeInterval (n : ℕ) : RatInterval :=
  let L := lowLogTwoInterval
  let p := lowKappaSqInterval n
  (pure 0 - (pure 4 * L * p - L - pure 4)) / (pure 16 * L)

private def lowCoreCoeffFourInterval (n : ℕ) : RatInterval :=
  let L := lowLogTwoInterval
  let p := lowKappaSqInterval n
  (pure 12 * L * p - L + pure 24 * p - pure 6) / (pure 64 * L)

private def lowCoreCoeffFiveInterval (n : ℕ) : RatInterval :=
  let L := lowLogTwoInterval
  let p := lowKappaSqInterval n
  let p2 := p * p
  (pure 16 * L * p2 - pure 24 * L * p + L - pure 96 * p + pure 8) /
    (pure 256 * L)

private theorem lowCoeffDenom_lower_pos
    {m : ℚ} (hm : 0 < m) :
    0 < (pure m * lowLogTwoInterval).lower := by
  apply mul_lower_pos_of_pos
  · simpa only [RatInterval.pure] using hm
  · norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval]
  · exact valid_of_contains (contains_pure m)
  · exact valid_of_contains lowLogTwoInterval_contains

private theorem lowCoreCoeffThreeInterval_contains (n : ℕ) :
    (lowCoreCoeffThreeInterval n).Contains
      (diagonalCoreCoeffThree yoshidaLength (yoshidaKappa n ^ 2)) := by
  have hL := lowLogTwoInterval_contains
  have hp := lowKappaSqInterval_contains n
  unfold lowCoreCoeffThreeInterval diagonalCoreCoeffThree
  exact contains_div_of_pos (lowCoeffDenom_lower_pos (by norm_num))
    (by
      have hsub := contains_sub (contains_pure (0 : ℚ))
        (contains_sub
          (contains_sub
            (contains_mul (contains_mul (contains_pure 4) hL) hp) hL)
          (contains_pure 4))
      convert hsub using 1
      ring)
    (contains_mul (contains_pure 16) hL)

private theorem lowCoreCoeffFourInterval_contains (n : ℕ) :
    (lowCoreCoeffFourInterval n).Contains
      (diagonalCoreCoeffFour yoshidaLength (yoshidaKappa n ^ 2)) := by
  have hL := lowLogTwoInterval_contains
  have hp := lowKappaSqInterval_contains n
  unfold lowCoreCoeffFourInterval diagonalCoreCoeffFour
  exact contains_div_of_pos (lowCoeffDenom_lower_pos (by norm_num))
    (contains_sub
      (contains_add
        (contains_sub
          (contains_mul (contains_mul (contains_pure 12) hL) hp) hL)
        (contains_mul (contains_pure 24) hp))
      (contains_pure 6))
    (contains_mul (contains_pure 64) hL)

private theorem lowCoreCoeffFiveInterval_contains (n : ℕ) :
    (lowCoreCoeffFiveInterval n).Contains
      (diagonalCoreCoeffFive yoshidaLength (yoshidaKappa n ^ 2)) := by
  have hL := lowLogTwoInterval_contains
  have hp := lowKappaSqInterval_contains n
  have hp2 : (lowKappaSqInterval n * lowKappaSqInterval n).Contains
      ((yoshidaKappa n ^ 2) ^ 2) := by
    convert contains_mul hp hp using 1
    ring
  unfold lowCoreCoeffFiveInterval diagonalCoreCoeffFive
  exact contains_div_of_pos (lowCoeffDenom_lower_pos (by norm_num))
    (contains_add
      (contains_sub
        (contains_add
          (contains_sub
            (contains_mul (contains_mul (contains_pure 16) hL) hp2)
            (contains_mul (contains_mul (contains_pure 24) hL) hp))
          hL)
        (contains_mul (contains_pure 96) hp))
      (contains_pure 8))
    (contains_mul (contains_pure 256) hL)

private def lowInvPow (x : ℝ) (p : ℕ) (j : ℕ) : ℝ :=
  1 / (x + j) ^ p

private def lowInvPowUpperPotential (x : ℝ) (p : ℕ) (j : ℕ) : ℝ :=
  (((p - 1 : ℕ) : ℝ))⁻¹ * lowInvPow x (p - 1) j +
    (1 / 2 : ℝ) * lowInvPow x p j +
    ((p : ℝ) / 12) * lowInvPow x (p + 1) j

private def lowInvPowLowerPotential (x : ℝ) (p : ℕ) (j : ℕ) : ℝ :=
  lowInvPowUpperPotential x p j -
    (((p * (p + 1) * (p + 2) : ℕ) : ℝ) / 720) *
      lowInvPow x (p + 3) j

private theorem summable_lowInvPow
    {x : ℝ} (hx : 0 < x) {p : ℕ} (hp : 1 < p) :
    Summable (lowInvPow x p) := by
  have hs := (Real.summable_one_div_nat_add_rpow x (p : ℝ)).2 (by
    exact_mod_cast hp)
  apply hs.congr
  intro j
  rw [lowInvPow, abs_of_pos (by positivity : 0 < (j : ℝ) + x),
    Real.rpow_natCast]
  congr 2
  ring

private theorem tendsto_lowInvPow
    (x : ℝ) {p : ℕ} (hp : 0 < p) :
    Tendsto (lowInvPow x p) atTop (nhds 0) := by
  have htop : Tendsto (fun j : ℕ ↦ x + (j : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv : Tendsto (fun j : ℕ ↦ (x + (j : ℝ))⁻¹)
      atTop (nhds 0) := by
    simpa only [one_div] using htop.const_div_atTop 1
  have hpow := hinv.pow p
  convert hpow using 1
  · funext j
    rw [lowInvPow, one_div, inv_pow]
  · simp [hp.ne']

private theorem tendsto_lowInvPowUpperPotential
    (x : ℝ) {p : ℕ} (hp : 1 < p) :
    Tendsto (lowInvPowUpperPotential x p) atTop (nhds 0) := by
  have h1 := (tendsto_lowInvPow x (Nat.sub_pos_of_lt hp)).const_mul
    (((p - 1 : ℕ) : ℝ))⁻¹
  have h2 := (tendsto_lowInvPow x (by omega : 0 < p)).const_mul (1 / 2 : ℝ)
  have h3 := (tendsto_lowInvPow x (by omega : 0 < p + 1)).const_mul
    ((p : ℝ) / 12)
  change Tendsto
    (fun j : ℕ ↦ (((p - 1 : ℕ) : ℝ))⁻¹ * lowInvPow x (p - 1) j +
      (1 / 2 : ℝ) * lowInvPow x p j +
      ((p : ℝ) / 12) * lowInvPow x (p + 1) j) atTop (nhds 0)
  simpa only [mul_zero, add_zero] using (h1.add h2).add h3

private theorem tendsto_lowInvPowLowerPotential
    (x : ℝ) {p : ℕ} (hp : 1 < p) :
    Tendsto (lowInvPowLowerPotential x p) atTop (nhds 0) := by
  have hu := tendsto_lowInvPowUpperPotential x hp
  have hr := (tendsto_lowInvPow x (by omega : 0 < p + 3)).const_mul
    (((p * (p + 1) * (p + 2) : ℕ) : ℝ) / 720)
  change Tendsto
    (fun j : ℕ ↦ lowInvPowUpperPotential x p j -
      (((p * (p + 1) * (p + 2) : ℕ) : ℝ) / 720) *
        lowInvPow x (p + 3) j) atTop (nhds 0)
  simpa only [mul_zero, sub_zero] using hu.sub hr

private theorem lowInvPowLowerPotential_sub_succ_le
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p = 3 ∨ p = 4 ∨ p = 5) (j : ℕ) :
    lowInvPowLowerPotential x p j -
        lowInvPowLowerPotential x p (j + 1) ≤
      lowInvPow x p j := by
  let a : ℝ := x + j
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : 0 < a + 1 := by positivity
  have haOne : 1 ≤ a := by
    dsimp only [a]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  unfold lowInvPowLowerPotential lowInvPowUpperPotential lowInvPow
  rw [show x + (j : ℝ) = a by rfl,
    show x + ((j + 1 : ℕ) : ℝ) = a + 1 by
      dsimp only [a]
      push_cast
      ring]
  rcases hp with (rfl | rfl | rfl)
  all_goals dsimp
  all_goals field_simp [ha.ne', ha1.ne']
  all_goals ring_nf
  all_goals nlinarith [sq_nonneg (a - 1), sq_nonneg a,
    sq_nonneg (a ^ 2), sq_nonneg (a ^ 3), sq_nonneg (a ^ 4)]

private theorem lowInvPow_le_upperPotential_sub_succ
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p = 3 ∨ p = 4 ∨ p = 5) (j : ℕ) :
    lowInvPow x p j ≤
      lowInvPowUpperPotential x p j -
        lowInvPowUpperPotential x p (j + 1) := by
  let a : ℝ := x + j
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha1 : 0 < a + 1 := by positivity
  have haOne : 1 ≤ a := by
    dsimp only [a]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  unfold lowInvPowUpperPotential lowInvPow
  rw [show x + (j : ℝ) = a by rfl,
    show x + ((j + 1 : ℕ) : ℝ) = a + 1 by
      dsimp only [a]
      push_cast
      ring]
  rcases hp with (rfl | rfl | rfl)
  all_goals dsimp
  all_goals field_simp [ha.ne', ha1.ne']
  all_goals ring_nf
  all_goals nlinarith [sq_nonneg (a - 1), sq_nonneg a,
    sq_nonneg (a ^ 2), sq_nonneg (a ^ 3), sq_nonneg (a ^ 4)]

private theorem lowInvPow_tsum_bounds
    {x : ℝ} (hx : 1 ≤ x) {p : ℕ}
    (hp : p = 3 ∨ p = 4 ∨ p = 5) :
    lowInvPowLowerPotential x p 0 ≤ ∑' j : ℕ, lowInvPow x p j ∧
      (∑' j : ℕ, lowInvPow x p j) ≤ lowInvPowUpperPotential x p 0 := by
  have hp1 : 1 < p := by
    rcases hp with (rfl | rfl | rfl)
    all_goals omega
  have hs := summable_lowInvPow (lt_of_lt_of_le (by norm_num) hx) hp1
  have hpartialLower (N : ℕ) :
      lowInvPowLowerPotential x p 0 - lowInvPowLowerPotential x p N ≤
        ∑ j ∈ Finset.range N, lowInvPow x p j := by
    rw [← Finset.sum_range_sub' (lowInvPowLowerPotential x p)]
    exact Finset.sum_le_sum fun j _ ↦
      lowInvPowLowerPotential_sub_succ_le hx hp j
  have hpartialUpper (N : ℕ) :
      (∑ j ∈ Finset.range N, lowInvPow x p j) ≤
        lowInvPowUpperPotential x p 0 - lowInvPowUpperPotential x p N := by
    rw [← Finset.sum_range_sub' (lowInvPowUpperPotential x p)]
    exact Finset.sum_le_sum fun j _ ↦
      lowInvPow_le_upperPotential_sub_succ hx hp j
  have hsum := hs.hasSum.tendsto_sum_nat
  have hlo : Tendsto
      (fun N : ℕ ↦ lowInvPowLowerPotential x p 0 -
        lowInvPowLowerPotential x p N) atTop
      (nhds (lowInvPowLowerPotential x p 0)) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_lowInvPowLowerPotential x hp1))
  have hup : Tendsto
      (fun N : ℕ ↦ lowInvPowUpperPotential x p 0 -
        lowInvPowUpperPotential x p N) atTop
      (nhds (lowInvPowUpperPotential x p 0)) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_lowInvPowUpperPotential x hp1))
  exact ⟨le_of_tendsto_of_tendsto (by simpa using hlo) hsum
      (Filter.Eventually.of_forall hpartialLower),
    le_of_tendsto_of_tendsto hsum (by simpa using hup)
      (Filter.Eventually.of_forall hpartialUpper)⟩

private def lowInvPowUpperQ (N p : ℕ) : ℚ :=
  (((p - 1 : ℕ) : ℚ))⁻¹ * (1 / (N : ℚ) ^ (p - 1)) +
    (1 / 2) * (1 / (N : ℚ) ^ p) +
    (p / 12) * (1 / (N : ℚ) ^ (p + 1))

private def lowInvPowLowerQ (N p : ℕ) : ℚ :=
  lowInvPowUpperQ N p -
    ((p * (p + 1) * (p + 2) : ℕ) / 720) *
      (1 / (N : ℚ) ^ (p + 3))

private def lowInvPowTailInterval (N p : ℕ) : RatInterval :=
  ⟨lowInvPowLowerQ N p, lowInvPowUpperQ N p⟩

private theorem lowInvPowTailInterval_contains
    {N p : ℕ} (hN : 1 ≤ N) (hp : p = 3 ∨ p = 4 ∨ p = 5) :
    (lowInvPowTailInterval N p).Contains
      (∑' j : ℕ, diagonalInvPow N p j) := by
  have h := lowInvPow_tsum_bounds (x := (N : ℝ)) (by exact_mod_cast hN) hp
  have hfun : (fun j : ℕ ↦ lowInvPow (N : ℝ) p j) =
      diagonalInvPow N p := by
    funext j
    unfold lowInvPow diagonalInvPow
    norm_num only [Nat.cast_add]
  rw [hfun] at h
  unfold lowInvPowTailInterval Contains lowInvPowLowerQ lowInvPowUpperQ
  norm_num only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
  simpa [lowInvPowLowerPotential, lowInvPowUpperPotential, lowInvPow] using h

private def lowHigherMainTailInterval (n N : ℕ) : RatInterval :=
  lowCoreCoeffThreeInterval n * lowInvPowTailInterval N 3 +
    lowCoreCoeffFourInterval n * lowInvPowTailInterval N 4 +
    lowCoreCoeffFiveInterval n * lowInvPowTailInterval N 5

private theorem lowHigherMainTailInterval_contains
    {n N : ℕ} (hN : 1 ≤ N) :
    (lowHigherMainTailInterval n N).Contains
      (diagonalHigherMainTail yoshidaLength (yoshidaKappa n ^ 2) N) := by
  unfold lowHigherMainTailInterval diagonalHigherMainTail
  exact contains_add
    (contains_add
      (contains_mul (lowCoreCoeffThreeInterval_contains n)
        (lowInvPowTailInterval_contains hN (Or.inl rfl)))
      (contains_mul (lowCoreCoeffFourInterval_contains n)
        (lowInvPowTailInterval_contains hN (Or.inr (Or.inl rfl)))))
    (contains_mul (lowCoreCoeffFiveInterval_contains n)
      (lowInvPowTailInterval_contains hN (Or.inr (Or.inr rfl))))

private def lowHigherTailScaleInterval (n N : ℕ) : RatInterval :=
  let P := lowKappaSqInterval n + pure 1
  let P2 := P * P
  let P3 := P2 * P
  let P4 := P3 * P
  P2 / pure ((N : ℚ) ^ 3) + P3 / pure ((N : ℚ) ^ 4) +
    P3 / pure ((N : ℚ) ^ 5) + (P4 + pure 2) / pure ((N : ℚ) ^ 6)

private def lowHigherResidualRadiusInterval (n N : ℕ) : RatInterval :=
  pure 11 * lowHigherTailScaleInterval n N /
    (pure 20 * pure ((N : ℚ) ^ 2))

private theorem lowHigherResidualRadiusInterval_contains
    {n N : ℕ} (hN : 1 ≤ N) :
    (lowHigherResidualRadiusInterval n N).Contains
      (diagonalHigherResidualTailRadius (yoshidaKappa n ^ 2) N) := by
  have hp := lowKappaSqInterval_contains n
  have hone : (RatInterval.pure (1 : ℚ)).Contains (1 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have htwo : (RatInterval.pure (2 : ℚ)).Contains (2 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have h11 : (RatInterval.pure (11 : ℚ)).Contains (11 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have h20 : (RatInterval.pure (20 : ℚ)).Contains (20 : ℝ) := by
    norm_num [Contains, RatInterval.pure]
  have hP := contains_add hp hone
  have hP2 := contains_mul hP hP
  have hP3 := contains_mul hP2 hP
  have hP4 := contains_mul hP3 hP
  have hP2' : ((lowKappaSqInterval n + RatInterval.pure 1) *
      (lowKappaSqInterval n + RatInterval.pure 1)).Contains
        ((yoshidaKappa n ^ 2 + 1) ^ 2) := by
    convert hP2 using 1
    ring
  have hP3' : ((lowKappaSqInterval n + RatInterval.pure 1) *
      (lowKappaSqInterval n + RatInterval.pure 1) *
        (lowKappaSqInterval n + RatInterval.pure 1)).Contains
        ((yoshidaKappa n ^ 2 + 1) ^ 3) := by
    convert hP3 using 1
    ring
  have hP4' : ((lowKappaSqInterval n + RatInterval.pure 1) *
      (lowKappaSqInterval n + RatInterval.pure 1) *
        (lowKappaSqInterval n + RatInterval.pure 1) *
        (lowKappaSqInterval n + RatInterval.pure 1)).Contains
          ((yoshidaKappa n ^ 2 + 1) ^ 4) := by
    convert hP4 using 1
    ring
  have hN2 : (RatInterval.pure ((N : ℚ) ^ 2)).Contains ((N : ℝ) ^ 2) := by
    norm_num [Contains, RatInterval.pure]
  have hN3 : (RatInterval.pure ((N : ℚ) ^ 3)).Contains ((N : ℝ) ^ 3) := by
    norm_num [Contains, RatInterval.pure]
  have hN4 : (RatInterval.pure ((N : ℚ) ^ 4)).Contains ((N : ℝ) ^ 4) := by
    norm_num [Contains, RatInterval.pure]
  have hN5 : (RatInterval.pure ((N : ℚ) ^ 5)).Contains ((N : ℝ) ^ 5) := by
    norm_num [Contains, RatInterval.pure]
  have hN6 : (RatInterval.pure ((N : ℚ) ^ 6)).Contains ((N : ℝ) ^ 6) := by
    norm_num [Contains, RatInterval.pure]
  have hN3pos : 0 < (N : ℚ) ^ 3 := by positivity
  have hN4pos : 0 < (N : ℚ) ^ 4 := by positivity
  have hN5pos : 0 < (N : ℚ) ^ 5 := by positivity
  have hN6pos : 0 < (N : ℚ) ^ 6 := by positivity
  have hscale : (lowHigherTailScaleInterval n N).Contains
      (diagonalHigherTailScale (yoshidaKappa n ^ 2) N) := by
    unfold lowHigherTailScaleInterval diagonalHigherTailScale
    exact contains_add
      (contains_add
        (contains_add
          (contains_div_of_pos hN3pos hP2' hN3)
          (contains_div_of_pos hN4pos hP3' hN4))
        (contains_div_of_pos hN5pos hP3' hN5))
      (contains_div_of_pos hN6pos (contains_add hP4' htwo) hN6)
  unfold lowHigherResidualRadiusInterval diagonalHigherResidualTailRadius
  exact contains_div_of_pos (by
      apply mul_lower_pos_of_pos
      · norm_num [RatInterval.pure]
      · norm_num [RatInterval.pure]
        positivity
      · exact valid_of_contains h20
      · exact valid_of_contains hN2)
    (contains_mul h11 hscale) (contains_mul h20 hN2)

private def lowHigherTailInterval (n N : ℕ) : RatInterval :=
  let r := (lowHigherResidualRadiusInterval n N).upper
  lowHigherMainTailInterval n N + ⟨-r, r⟩

private theorem lowHigherTailInterval_contains
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    (lowHigherTailInterval n N).Contains
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) := by
  have hmain := lowHigherMainTailInterval_contains (n := n) (by omega : 1 ≤ N)
  have hradI := lowHigherResidualRadiusInterval_contains
    (n := n) (by omega : 1 ≤ N)
  have herr := yoshidaDiagonalCorrection_tail_sub_higherMainTail_abs_le hN hmode
  let r : ℝ := ((lowHigherResidualRadiusInterval n N).upper : ℚ)
  have hradius : diagonalHigherResidualTailRadius (yoshidaKappa n ^ 2) N ≤ r :=
    hradI.2
  have he : -r ≤
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) -
        diagonalHigherMainTail yoshidaLength (yoshidaKappa n ^ 2) N ∧
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) -
        diagonalHigherMainTail yoshidaLength (yoshidaKappa n ^ 2) N ≤ r := by
    rw [abs_le] at herr
    constructor <;> linarith
  have heI : (⟨-(lowHigherResidualRadiusInterval n N).upper,
      (lowHigherResidualRadiusInterval n N).upper⟩ : RatInterval).Contains
        ((∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) -
          diagonalHigherMainTail yoshidaLength (yoshidaKappa n ^ 2) N) := by
    simpa only [Contains, Rat.cast_neg] using he
  unfold lowHigherTailInterval
  have h := contains_add hmain heI
  convert h using 1
  ring

/-- The structural zero-mode identity, transferred to the production moment
definition.  This records explicitly why mode zero does not use the nonzero
accelerated-series derivation. -/
theorem yoshidaDiagonalMoment_zero_eq_stieltjesProfile :
    yoshidaDiagonalMoment 0 =
      structuralYoshidaStieltjesProfile 0 / yoshidaLength -
        (Real.eulerMascheroniConstant + Real.log Real.pi +
          Real.pi / 2 + 3 * yoshidaLength) := by
  have h :=
    structuralYoshidaDiagonalMoment_zero_eq_stieltjesProfile_zero_sub_constant
  have hbridge : structuralYoshidaDiagonalMoment 0 =
      yoshidaDiagonalMoment 0 := by
    rfl
  rw [hbridge] at h
  simpa only [structuralYoshidaLength, yoshidaLength] using h

/-- Number of automatically rounded 256-term checkpoints used at each mode. -/
def lowDiagonalBlocks (n : ℕ) : ℕ :=
  if n = 0 then 2
  else if n ≤ 2 then 4
  else if n ≤ 4 then 8
  else if n ≤ 10 then 16
  else if n ≤ 20 then 32
  else if n ≤ 42 then 64
  else 128

/-- The fixed grid keeps all checkpoint denominators compact while adding at
most `2 · 10⁻¹⁶` width per block. -/
def lowDiagonalRoundingScale : ℚ := 10000000000000000

private theorem lowDiagonalBlocks_pos (n : ℕ) : 0 < lowDiagonalBlocks n := by
  unfold lowDiagonalBlocks
  split_ifs <;> norm_num

private theorem lowDiagonalCutoff_ge_sixteen (n : ℕ) :
    16 ≤ 256 * lowDiagonalBlocks n := by
  have h := lowDiagonalBlocks_pos n
  omega

private theorem ten_mul_mode_le_lowDiagonalCutoff
    {n : ℕ} (hn59 : n ≤ 59) :
    10 * n ≤ 256 * lowDiagonalBlocks n := by
  unfold lowDiagonalBlocks
  split_ifs <;> omega

private theorem lowDiagonalCorrection_summable
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    Summable (fun j : ℕ ↦
      yoshidaDiagonalDyadicPairedCorrection n (j + 1)) := by
  have habs := summable_abs_diagonalAcceleratedCorrection_of_tail
    (n := n) (N := N) hN hmode
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs] using habs

private theorem lowDiagonalCorrection_head_add_tail_eq_tsum
    {n N : ℕ} (hN : 16 ≤ N) (hmode : 10 * n ≤ N) :
    (∑ j ∈ Finset.range (N - 1),
        yoshidaDiagonalDyadicPairedCorrection n (1 + j)) +
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) =
        ∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (j + 1) := by
  have hsplit := (lowDiagonalCorrection_summable hN hmode).sum_add_tsum_nat_add
    (N - 1)
  have hhead :
      (∑ j ∈ Finset.range (N - 1),
          yoshidaDiagonalDyadicPairedCorrection n (1 + j)) =
        ∑ j ∈ Finset.range (N - 1),
          yoshidaDiagonalDyadicPairedCorrection n (j + 1) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    omega
  have htail :
      (∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (N + j)) =
        ∑' j : ℕ,
          yoshidaDiagonalDyadicPairedCorrection n (j + (N - 1) + 1) := by
    apply tsum_congr
    intro j
    congr 1
    omega
  rw [hhead, htail]
  exact hsplit

/-- Compact direct target for one low diagonal mode. -/
def yoshidaFactorTwoCleanLowDiagonalTarget (n : ℕ) : RatInterval :=
  let blocks := lowDiagonalBlocks n
  let N := 256 * blocks
  lowDiagonalBaseInterval n -
      coarseCheckpointHead
        (lowRoundedChunkBox n blocks lowDiagonalRoundingScale) blocks -
    lowHigherTailInterval n N

private theorem coarseCheckpointHead_width_eq_sum
    (box : ℕ → RatInterval) (chunks : ℕ) :
    width (coarseCheckpointHead box chunks) =
      ∑ i ∈ Finset.range chunks, width (box i) := by
  induction chunks with
  | zero =>
      rw [coarseCheckpointHead, width_pure]
      simp
  | succ chunks ih =>
      rw [coarseCheckpointHead, width_add, ih, Finset.sum_range_succ]

private theorem lowDiagonalTarget_width_eq (n : ℕ) :
    width (yoshidaFactorTwoCleanLowDiagonalTarget n) =
      width (lowDiagonalBaseInterval n) +
          (∑ i ∈ Finset.range (lowDiagonalBlocks n),
            width (lowRoundedChunkBox n (lowDiagonalBlocks n)
              lowDiagonalRoundingScale i)) +
        width (lowHigherTailInterval n (256 * lowDiagonalBlocks n)) := by
  unfold yoshidaFactorTwoCleanLowDiagonalTarget
  dsimp only
  rw [width_sub, width_sub, coarseCheckpointHead_width_eq_sum]

/-! ## Structural width estimates -/

private structure LowIntervalMetrics (I : RatInterval) (B W : ℚ) : Prop where
  valid : I.Valid
  absBound : I.AbsBound B
  width_le : width I ≤ W
  bound_nonneg : 0 ≤ B
  width_nonneg : 0 ≤ W

private theorem lowMetrics_pure {q B : ℚ} (hq : |q| ≤ B) (hB : 0 ≤ B) :
    LowIntervalMetrics (pure q) B 0 := by
  exact ⟨valid_pure q, absBound_pure hq, by rw [width_pure], hB, le_rfl⟩

private theorem LowIntervalMetrics.weaken
    {I : RatInterval} {B W B' W' : ℚ}
    (h : LowIntervalMetrics I B W) (hB : B ≤ B') (hW : W ≤ W') :
    LowIntervalMetrics I B' W' := by
  refine ⟨h.valid, ?_, h.width_le.trans hW,
    h.bound_nonneg.trans hB, h.width_nonneg.trans hW⟩
  rcases h.absBound with ⟨hl, hu⟩
  exact ⟨by linarith, hu.trans hB⟩

private theorem lowMetrics_add
    {I J : RatInterval} {BI BJ WI WJ : ℚ}
    (hI : LowIntervalMetrics I BI WI) (hJ : LowIntervalMetrics J BJ WJ) :
    LowIntervalMetrics (I + J) (BI + BJ) (WI + WJ) := by
  refine ⟨valid_add hI.valid hJ.valid,
    absBound_add hI.absBound hJ.absBound, ?_,
    add_nonneg hI.bound_nonneg hJ.bound_nonneg,
    add_nonneg hI.width_nonneg hJ.width_nonneg⟩
  rw [width_add]
  exact add_le_add hI.width_le hJ.width_le

private theorem lowMetrics_sub
    {I J : RatInterval} {BI BJ WI WJ : ℚ}
    (hI : LowIntervalMetrics I BI WI) (hJ : LowIntervalMetrics J BJ WJ) :
    LowIntervalMetrics (I - J) (BI + BJ) (WI + WJ) := by
  refine ⟨valid_sub hI.valid hJ.valid,
    absBound_sub hI.absBound hJ.absBound, ?_,
    add_nonneg hI.bound_nonneg hJ.bound_nonneg,
    add_nonneg hI.width_nonneg hJ.width_nonneg⟩
  rw [width_sub]
  exact add_le_add hI.width_le hJ.width_le

private theorem lowMetrics_mul
    {I J : RatInterval} {BI BJ WI WJ : ℚ}
    (hI : LowIntervalMetrics I BI WI) (hJ : LowIntervalMetrics J BJ WJ) :
    LowIntervalMetrics (I * J) (BI * BJ) (BJ * WI + BI * WJ) := by
  refine ⟨valid_mul hI.valid hJ.valid,
    absBound_mul hI.valid hJ.valid hI.absBound hJ.absBound
      hI.bound_nonneg hJ.bound_nonneg, ?_,
    mul_nonneg hI.bound_nonneg hJ.bound_nonneg,
    add_nonneg (mul_nonneg hJ.bound_nonneg hI.width_nonneg)
      (mul_nonneg hI.bound_nonneg hJ.width_nonneg)⟩
  calc
    width (I * J) ≤ BJ * width I + BI * width J :=
      width_mul_le hI.valid hJ.valid hI.absBound hJ.absBound
        hI.bound_nonneg hJ.bound_nonneg
    _ ≤ BJ * WI + BI * WJ :=
      add_le_add
        (mul_le_mul_of_nonneg_left hI.width_le hJ.bound_nonneg)
        (mul_le_mul_of_nonneg_left hJ.width_le hI.bound_nonneg)

private theorem lowMetrics_inv
    {I : RatInterval} {B W m : ℚ}
    (hI : LowIntervalMetrics I B W) (hm : 0 < m) (hml : m ≤ I.lower) :
    LowIntervalMetrics I⁻¹ m⁻¹ (W / m ^ 2) := by
  have hl : 0 < I.lower := hm.trans_le hml
  refine ⟨valid_inv_of_pos hI.valid hl,
    absBound_inv_of_lower hI.valid hm hml, ?_,
    inv_nonneg.mpr hm.le, div_nonneg hI.width_nonneg (sq_nonneg m)⟩
  calc
    width I⁻¹ ≤ width I / (m * m) :=
      width_inv_le_of_lower hI.valid hm hml
    _ ≤ W / (m * m) :=
      div_le_div_of_nonneg_right hI.width_le (mul_nonneg hm.le hm.le)
    _ = W / m ^ 2 := by rw [pow_two]

private theorem lowMetrics_div
    {I J : RatInterval} {BI BJ WI WJ m : ℚ}
    (hI : LowIntervalMetrics I BI WI) (hJ : LowIntervalMetrics J BJ WJ)
    (hm : 0 < m) (hml : m ≤ J.lower) :
    LowIntervalMetrics (I / J) (BI * m⁻¹)
      (m⁻¹ * WI + BI * (WJ / m ^ 2)) := by
  exact lowMetrics_mul hI (lowMetrics_inv hJ hm hml)

private theorem lowMetrics_positiveSquare
    {I : RatInterval} {B W : ℚ}
    (hI : LowIntervalMetrics I B W) (hI0 : 0 ≤ I.lower) :
    LowIntervalMetrics (lowPositiveSquare I) (B ^ 2) (2 * B * W) := by
  have hIu0 : 0 ≤ I.upper := hI0.trans hI.valid
  have hlB : I.lower ≤ B := hI.valid.trans hI.absBound.2
  have huB : I.upper ≤ B := hI.absBound.2
  refine ⟨?_, ?_, ?_, sq_nonneg B,
    mul_nonneg (mul_nonneg (by norm_num) hI.bound_nonneg)
      hI.width_nonneg⟩
  · unfold lowPositiveSquare RatInterval.Valid
    have hprod : 0 ≤ (I.upper - I.lower) * (I.upper + I.lower) :=
      mul_nonneg (sub_nonneg.mpr hI.valid) (add_nonneg hIu0 hI0)
    nlinarith
  · unfold lowPositiveSquare AbsBound
    constructor <;> nlinarith [sq_nonneg I.lower, sq_nonneg I.upper]
  · unfold lowPositiveSquare width
    have hfactor :
        I.upper ^ 2 - I.lower ^ 2 =
          (I.upper - I.lower) * (I.upper + I.lower) := by ring
    rw [hfactor]
    have hsum : I.upper + I.lower ≤ 2 * B := by linarith
    have hdiff : I.upper - I.lower ≤ W := hI.width_le
    nlinarith [mul_nonneg (sub_nonneg.mpr hI.valid)
      (add_nonneg hIu0 hI0),
      mul_le_mul hdiff hsum (add_nonneg hIu0 hI0)
        hI.width_nonneg]

private theorem lowLogTwo_metrics :
    LowIntervalMetrics lowLogTwoInterval 1 (1 / 100000000000000) := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
    norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval,
      RatInterval.Valid, AbsBound, width]

private theorem lowLogTwo_lower :
    (2 / 3 : ℚ) ≤ lowLogTwoInterval.lower := by
  norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval]

private theorem lowY_metrics (n : ℕ) :
    LowIntervalMetrics (lowYInterval n) ((229 / 50 : ℚ) * n)
      ((n : ℚ) / 10000000000000) := by
  refine ⟨?_, ?_, ?_, by positivity, by positivity⟩
  · unfold lowYInterval
    norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval,
      piFineInterval, RatInterval.Valid]
    have hn0 : (0 : ℚ) ≤ n := by positivity
    nlinarith
  · unfold lowYInterval AbsBound
    constructor
    · norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval,
        piFineInterval]
      have hn0 : (0 : ℚ) ≤ n := by positivity
      nlinarith
    · norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval,
        piFineInterval]
      have hn0 : (0 : ℚ) ≤ n := by positivity
      nlinarith
  · unfold lowYInterval width
    norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval,
      piFineInterval]
    have hn0 : (0 : ℚ) ≤ n := by positivity
    nlinarith

private theorem lowY_lower (n : ℕ) :
    (9 / 2 : ℚ) * n ≤ (lowYInterval n).lower := by
  unfold lowYInterval
  norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval, piFineInterval]
  have hn0 : (0 : ℚ) ≤ n := by positivity
  nlinarith

private theorem lowKappaSq_metrics (n : ℕ) :
    LowIntervalMetrics (lowKappaSqInterval n) (100 * (n : ℚ) ^ 2)
      ((n : ℚ) ^ 2 / 100000000000) := by
  have hy := lowY_metrics n
  have hy0 := lowYInterval_lower_nonneg n
  have hsq := lowMetrics_positiveSquare hy hy0
  have hfour := lowMetrics_pure (q := (4 : ℚ)) (B := 4) (by norm_num)
    (by norm_num)
  have h := lowMetrics_mul hfour hsq
  unfold lowKappaSqInterval
  apply h.weaken
  · have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
    norm_num
    nlinarith
  · have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
    norm_num
    nlinarith

private theorem lowKappaSq_metrics_sharp (n : ℕ) :
    LowIntervalMetrics (lowKappaSqInterval n) (84 * (n : ℚ) ^ 2)
      ((n : ℚ) ^ 2 / 100000000000) := by
  have hy := lowY_metrics n
  have hy0 := lowYInterval_lower_nonneg n
  have hsq := lowMetrics_positiveSquare hy hy0
  have hfour := lowMetrics_pure (q := (4 : ℚ)) (B := 4) (by norm_num)
    (by norm_num)
  have h := lowMetrics_mul hfour hsq
  unfold lowKappaSqInterval
  apply h.weaken
  · have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
    norm_num
    nlinarith
  · have hn2 : (0 : ℚ) ≤ (n : ℚ) ^ 2 := sq_nonneg _
    norm_num
    nlinarith

private theorem lowKappaSq_lower (n : ℕ) :
    64 * (n : ℚ) ^ 2 ≤ (lowKappaSqInterval n).lower := by
  have hylo := lowY_lower n
  have hyv := (lowY_metrics n).valid
  have hynonneg : (0 : ℚ) ≤ (lowYInterval n).lower :=
    lowYInterval_lower_nonneg n
  have hyunonneg : (0 : ℚ) ≤ (lowYInterval n).upper :=
    hynonneg.trans hyv
  have hn0 : (0 : ℚ) ≤ n := by positivity
  have hl4 : (4 : ℚ) * n ≤ (lowYInterval n).lower := by
    linarith
  have hu4 : (4 : ℚ) * n ≤ (lowYInterval n).upper :=
    hl4.trans hyv
  have hlsq : ((4 : ℚ) * n) ^ 2 ≤ (lowYInterval n).lower ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hn0) hl4 2
  have husq : ((4 : ℚ) * n) ^ 2 ≤ (lowYInterval n).upper ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hn0) hu4 2
  have hll : 64 * (n : ℚ) ^ 2 ≤
      4 * (lowYInterval n).lower ^ 2 := by nlinarith
  have hlu : 64 * (n : ℚ) ^ 2 ≤
      4 * (lowYInterval n).upper ^ 2 := by nlinarith
  unfold lowKappaSqInterval lowPositiveSquare
  change 64 * (n : ℚ) ^ 2 ≤
    min (min (4 * (lowYInterval n).lower ^ 2)
      (4 * (lowYInterval n).upper ^ 2))
      (min (4 * (lowYInterval n).lower ^ 2)
        (4 * (lowYInterval n).upper ^ 2))
  exact le_min (le_min hll hlu) (le_min hll hlu)

private theorem lowSqrtTwo_metrics :
    LowIntervalMetrics sqrtTwoInterval (3 / 2) (1 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
    norm_num [sqrtTwoInterval, RatInterval.Valid, AbsBound, width]

private theorem lowSqrtTwo_lower :
    (7 / 5 : ℚ) ≤ sqrtTwoInterval.lower := by
  norm_num [sqrtTwoInterval]

private theorem lowSqrtDyadic_metrics (k : ℕ) :
    LowIntervalMetrics (sqrtDyadicInterval k) 1
      (1 / 1000000000000000) := by
  unfold sqrtDyadicInterval
  split_ifs with hk32
  · let d : ℚ := (4 : ℚ) ^ k
    have hd : 0 < d := by dsimp only [d]; positivity
    have hd1 : (1 : ℚ) ≤ d := by
      dsimp only [d]
      exact one_le_pow₀ (by norm_num)
    have hdinv : d⁻¹ ≤ 1 := by
      simpa only [one_div, inv_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1) hd1
    have hinv := lowMetrics_inv lowSqrtTwo_metrics
      (by norm_num : (0 : ℚ) < 7 / 5) lowSqrtTwo_lower
    have hden := lowMetrics_pure (q := d) (B := d)
      (by rw [abs_of_pos hd]) hd.le
    have h := lowMetrics_div hinv hden hd (by simp [d, RatInterval.pure])
    apply h.weaken
    · dsimp only [d] at hdinv ⊢
      norm_num at hdinv ⊢
      nlinarith
    · dsimp only [d] at hdinv ⊢
      norm_num at hdinv ⊢
      nlinarith
  · refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
      norm_num [tinyDyadic, RatInterval.Valid, AbsBound, width]

private theorem lowDyadic_metrics (k : ℕ) :
    LowIntervalMetrics (dyadicInterval k) 1
      (1 / 10000000000000000000) := by
  unfold dyadicInterval
  split_ifs with hk32
  · have hd : 0 < (4 : ℚ) ^ k := by positivity
    have hd1 : (1 : ℚ) ≤ (4 : ℚ) ^ k :=
      one_le_pow₀ (by norm_num)
    apply (lowMetrics_pure (q := 1 / (4 : ℚ) ^ k) (B := 1) ?_
      (by norm_num)).weaken le_rfl (by norm_num)
    rw [abs_of_pos (div_pos (by norm_num) hd)]
    exact (div_le_one hd).2 hd1
  · refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
      norm_num [tinyDyadic, RatInterval.Valid, AbsBound, width]

private theorem lowDiagonalA_metrics :
    LowIntervalMetrics lowDiagonalAInterval 1
      (1 / 10000000000000) := by
  have htwo := lowMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have hden := lowMetrics_mul htwo lowLogTwo_metrics
  have hdenLower : (4 / 3 : ℚ) ≤
      (pure 2 * lowLogTwoInterval).lower := by
    change (4 / 3 : ℚ) ≤ min (min (2 * lowLogTwoInterval.lower)
      (2 * lowLogTwoInterval.upper))
      (min (2 * lowLogTwoInterval.lower) (2 * lowLogTwoInterval.upper))
    have hv := lowLogTwo_metrics.valid
    have hlo := lowLogTwo_lower
    have hup : (2 / 3 : ℚ) ≤ lowLogTwoInterval.upper := hlo.trans hv
    apply le_min <;> apply le_min <;> nlinarith
  have hone := lowMetrics_pure (q := (1 : ℚ)) (B := 1)
    (by norm_num) (by norm_num)
  have hquot := lowMetrics_div hone hden
    (by norm_num : (0 : ℚ) < 4 / 3) hdenLower
  have hquarter := lowMetrics_pure (q := (1 / 4 : ℚ)) (B := 1 / 4)
    (by norm_num) (by norm_num)
  have h := lowMetrics_add hquot hquarter
  unfold lowDiagonalAInterval
  apply h.weaken <;> norm_num

private theorem lowDiagonalRamp_metrics_pos
    (n k : ℕ) (hk : 1 ≤ k) :
    let a : ℚ := 2 * (k : ℚ) + 1 / 2
    let t : ℚ := a ^ 2 + 64 * (n : ℚ) ^ 2
    LowIntervalMetrics
      (lowDiagonalRampInterval n a (sqrtDyadicInterval k))
      (9 * a / t) (a / (100000000000 * t)) := by
  let a : ℚ := 2 * (k : ℚ) + 1 / 2
  let m : ℚ := (n : ℚ) ^ 2
  let x : ℚ := a ^ 2
  let t : ℚ := x + 64 * m
  change LowIntervalMetrics
    (lowDiagonalRampInterval n a (sqrtDyadicInterval k))
    (9 * a / t) (a / (100000000000 * t))
  have ha : (5 / 2 : ℚ) ≤ a := by
    dsimp only [a]
    have hkq : (1 : ℚ) ≤ k := by exact_mod_cast hk
    linarith
  have ha0 : 0 < a := (by norm_num : (0 : ℚ) < 5 / 2).trans_le ha
  have hm0 : 0 ≤ m := by dsimp only [m]; positivity
  have hx0 : 0 < x := by dsimp only [x]; positivity
  have ht0 : 0 < t := by dsimp only [t]; positivity
  have hp : LowIntervalMetrics (lowKappaSqInterval n) (100 * m)
      (m / 100000000000) := by
    simpa only [m] using lowKappaSq_metrics n
  have hq := lowSqrtDyadic_metrics k
  have hone := lowMetrics_pure (q := (1 : ℚ)) (B := 1)
    (by norm_num) (by norm_num)
  have haI := lowMetrics_pure (q := a) (B := a)
    (by rw [abs_of_pos ha0]) ha0.le
  have hxI := lowMetrics_pure (q := x) (B := x)
    (by rw [abs_of_pos hx0]) hx0.le
  have htwo := lowMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have hshift := lowMetrics_add (lowMetrics_sub hq hone)
    (lowMetrics_mul haI lowLogTwo_metrics)
  have hdiff := lowMetrics_sub hxI hp
  have htermOne := lowMetrics_mul hshift hdiff
  have htermTwo := lowMetrics_mul
    (lowMetrics_mul (lowMetrics_mul htwo haI) hp) lowLogTwo_metrics
  have hnum := lowMetrics_add htermOne htermTwo
  have hnumB := hnum.bound_nonneg
  have hnum' : LowIntervalMetrics
      (((sqrtDyadicInterval k - RatInterval.pure 1 +
          RatInterval.pure a * lowLogTwoInterval) *
          (RatInterval.pure x - lowKappaSqInterval n) +
        RatInterval.pure 2 * RatInterval.pure a * lowKappaSqInterval n *
          lowLogTwoInterval))
      (6 * a * t) (7 * a * t / 10000000000000) := by
    apply hnum.weaken
    · have hfirst : 0 ≤ x * (5 * a - 2) :=
        mul_nonneg hx0.le (by nlinarith)
      have hsecond : 0 ≤ m * (84 * a - 200) := by
        apply mul_nonneg hm0
        nlinarith
      dsimp only [t]
      norm_num at hnumB ⊢
      nlinarith
    · have hfirst : 0 ≤ x * (690 * a - 1) :=
        mul_nonneg hx0.le (by nlinarith)
      have hsecond : 0 ≤ m * (11800 * a - 20100) := by
        apply mul_nonneg hm0
        nlinarith
      dsimp only [t]
      norm_num
      nlinarith
  have hsum := lowMetrics_add hxI hp
  have hsum0 : 0 ≤
      (RatInterval.pure x + lowKappaSqInterval n).lower := by
    change 0 ≤ x + (lowKappaSqInterval n).lower
    exact add_nonneg hx0.le (lowKappaSqInterval_lower_nonneg n)
  have hsq := lowMetrics_positiveSquare hsum hsum0
  have hden := lowMetrics_mul lowLogTwo_metrics hsq
  have hden' : LowIntervalMetrics
      (lowLogTwoInterval *
        lowPositiveSquare (RatInterval.pure x + lowKappaSqInterval n))
      ((x + 100 * m) ^ 2) (6 * t ^ 2 / 10000000000000) := by
    exact hden.weaken (by norm_num) (by
      have hnonnegOne : 0 ≤ 59 * x ^ 2 := by positivity
      have hnonnegTwo : 0 ≤ 5480 * x * m := by
        positivity
      have hnonnegThree : 0 ≤ 35760 * m ^ 2 := by positivity
      norm_num
      nlinarith)
  let d : ℚ := (2 / 3) * t ^ 2
  have hd0 : 0 < d := by dsimp only [d]; positivity
  have hsumLower : t ≤
      (RatInterval.pure x + lowKappaSqInterval n).lower := by
    change x + 64 * m ≤ x + (lowKappaSqInterval n).lower
    have hpLower := lowKappaSq_lower n
    simpa only [m, add_comm] using add_le_add_left hpLower x
  have hsumUpper : t ≤
      (RatInterval.pure x + lowKappaSqInterval n).upper :=
    hsumLower.trans hsum.valid
  have hsquareLower : t ^ 2 ≤
      (lowPositiveSquare
        (RatInterval.pure x + lowKappaSqInterval n)).lower := by
    exact pow_le_pow_left₀ ht0.le hsumLower 2
  have hsquareUpper : t ^ 2 ≤
      (lowPositiveSquare
        (RatInterval.pure x + lowKappaSqInterval n)).upper := by
    exact pow_le_pow_left₀ ht0.le hsumUpper 2
  have hLupper : (2 / 3 : ℚ) ≤ lowLogTwoInterval.upper :=
    lowLogTwo_lower.trans lowLogTwo_metrics.valid
  have hLlower0 : (0 : ℚ) ≤ lowLogTwoInterval.lower :=
    (by norm_num : (0 : ℚ) ≤ 2 / 3).trans lowLogTwo_lower
  have hLupper0 : (0 : ℚ) ≤ lowLogTwoInterval.upper :=
    hLlower0.trans lowLogTwo_metrics.valid
  have hdenLower : d ≤
      (lowLogTwoInterval *
        lowPositiveSquare
          (RatInterval.pure x + lowKappaSqInterval n)).lower := by
    change d ≤ min
      (min (lowLogTwoInterval.lower *
          (lowPositiveSquare
            (RatInterval.pure x + lowKappaSqInterval n)).lower)
        (lowLogTwoInterval.lower *
          (lowPositiveSquare
            (RatInterval.pure x + lowKappaSqInterval n)).upper))
      (min (lowLogTwoInterval.upper *
          (lowPositiveSquare
            (RatInterval.pure x + lowKappaSqInterval n)).lower)
        (lowLogTwoInterval.upper *
          (lowPositiveSquare
            (RatInterval.pure x + lowKappaSqInterval n)).upper))
    dsimp only [d]
    apply le_min <;> apply le_min
    · exact mul_le_mul lowLogTwo_lower hsquareLower (sq_nonneg t) hLlower0
    · exact mul_le_mul lowLogTwo_lower hsquareUpper (sq_nonneg t) hLlower0
    · exact mul_le_mul hLupper hsquareLower (sq_nonneg t) hLupper0
    · exact mul_le_mul hLupper hsquareUpper (sq_nonneg t) hLupper0
  have hquot := lowMetrics_div hnum' hden' hd0 hdenLower
  have hquot' := hquot.weaken (B' := 9 * a / t)
    (W' := a / (100000000000 * t)) (by
      dsimp only [d]
      field_simp [ht0.ne']
      norm_num) (by
      dsimp only [d]
      field_simp [ht0.ne']
      nlinarith [ha0])
  simpa only [lowDiagonalRampInterval, m, x, t] using hquot'

private theorem lowDiagonalCorrection_width_le
    (n k : ℕ) (hk : 1 ≤ k) :
    width (lowDiagonalCorrectionInterval n k) ≤
      1 / (50000000000 * (k : ℚ)) := by
  let kq : ℚ := k
  let a : ℚ := 2 * kq + 1 / 2
  let t : ℚ := a ^ 2 + 64 * (n : ℚ) ^ 2
  have hkq : (1 : ℚ) ≤ kq := by
    dsimp only [kq]
    exact_mod_cast hk
  have hkq0 : 0 < kq := zero_lt_one.trans_le hkq
  have haLower : 2 * kq ≤ a := by dsimp only [a]; linarith
  have ha0 : 0 < a := (mul_pos (by norm_num) hkq0).trans_le haLower
  have ht0 : 0 < t := by dsimp only [t]; positivity
  have htLower : a ^ 2 ≤ t := by
    dsimp only [t]
    nlinarith [sq_nonneg (n : ℚ)]
  have hat : a / t ≤ 1 / (2 * kq) := by
    rw [div_le_iff₀ ht0, div_mul_eq_mul_div, le_div_iff₀ (mul_pos (by norm_num) hkq0)]
    have haa : 2 * kq * a ≤ a ^ 2 := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right haLower ha0.le
    simpa only [mul_comm, mul_left_comm, mul_assoc, one_mul] using
      haa.trans htLower
  have hramp : LowIntervalMetrics
      (lowDiagonalRampInterval n a (sqrtDyadicInterval k))
      (9 * a / t) (a / (100000000000 * t)) := by
    simpa only [a, t, kq] using lowDiagonalRamp_metrics_pos n k hk
  have htwo := lowMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have htworamp := lowMetrics_mul htwo hramp
  have hone := lowMetrics_pure (q := (1 : ℚ)) (B := 1)
    (by norm_num) (by norm_num)
  have hdyadic := lowDyadic_metrics k
  have hnumerator := lowMetrics_sub hone hdyadic
  have hkI := lowMetrics_pure (q := kq) (B := kq)
    (by rw [abs_of_pos hkq0]) hkq0.le
  have hquot := lowMetrics_div hnumerator hkI hkq0
    (by simp [RatInterval.pure])
  have hkSq0 : 0 < kq ^ 2 := sq_pos_of_pos hkq0
  have hkSqI := lowMetrics_pure (q := kq ^ 2) (B := kq ^ 2)
    (by rw [abs_of_pos hkSq0]) hkSq0.le
  have hAquot := lowMetrics_div lowDiagonalA_metrics hkSqI hkSq0
    (by simp [RatInterval.pure])
  have hcorr := lowMetrics_add (lowMetrics_sub htworamp hquot) hAquot
  have hkInvSq : 1 / kq ^ 2 ≤ 1 / kq := by
    apply one_div_le_one_div_of_le hkq0
    nlinarith [mul_le_mul_of_nonneg_right hkq hkq0.le]
  have hnumeric :
      2 * (a / (100000000000 * t)) +
          (1 / kq) * (1 / 10000000000000000000) +
          1 * (1 / 10000000000000 / (kq ^ 2)) ≤
        1 / (50000000000 * kq) := by
    have hrampScaled :
        2 * (a / (100000000000 * t)) ≤
          1 / (100000000000 * kq) := by
      calc
        2 * (a / (100000000000 * t)) =
            (2 / 100000000000) * (a / t) := by field_simp
        _ ≤ (2 / 100000000000) * (1 / (2 * kq)) := by
          gcongr
        _ = 1 / (100000000000 * kq) := by field_simp
    have hA :
        1 / 10000000000000 / kq ^ 2 ≤
          1 / 10000000000000 / kq := by
      calc
        1 / 10000000000000 / kq ^ 2 =
            (1 / 10000000000000) * (1 / kq ^ 2) := by ring
        _ ≤ (1 / 10000000000000) * (1 / kq) :=
          mul_le_mul_of_nonneg_left hkInvSq (by norm_num)
        _ = 1 / 10000000000000 / kq := by ring
    have hdyadicEq :
        (1 / kq) * (1 / 10000000000000000000) =
          1 / (10000000000000000000 * kq) := by
      field_simp [hkq0.ne']
    calc
      2 * (a / (100000000000 * t)) +
          (1 / kq) * (1 / 10000000000000000000) +
          1 * (1 / 10000000000000 / kq ^ 2) ≤
          1 / (100000000000 * kq) +
            1 / (10000000000000000000 * kq) +
            1 / (10000000000000 * kq) := by
        rw [hdyadicEq]
        have hAEq : 1 / 10000000000000 / kq =
            1 / (10000000000000 * kq) := by
          field_simp [hkq0.ne']
        rw [← hAEq]
        linarith
      _ ≤ 1 / (50000000000 * kq) := by
        field_simp [hkq0.ne']
        norm_num
  unfold lowDiagonalCorrectionInterval
  dsimp only
  exact hcorr.width_le.trans (by
    norm_num at hcorr ⊢
    simpa only [kq, one_div, div_eq_mul_inv, mul_inv_rev, one_mul, mul_one,
      mul_comm, mul_left_comm, mul_assoc] using hnumeric)

private theorem lowDiagonalHeadIntervalAux_width_eq
    (n fuel k : ℕ) (acc : RatInterval) :
    width (lowDiagonalHeadIntervalAux n fuel k acc) =
      width acc + ∑ j ∈ Finset.range fuel,
        width (lowDiagonalCorrectionInterval n (k + j)) := by
  induction fuel generalizing k acc with
  | zero => simp [lowDiagonalHeadIntervalAux]
  | succ fuel ih =>
      rw [lowDiagonalHeadIntervalAux, ih, width_add,
        Finset.sum_range_succ']
      have hshift :
          (∑ j ∈ Finset.range fuel,
              width (lowDiagonalCorrectionInterval n ((k + 1) + j))) =
            ∑ j ∈ Finset.range fuel,
              width (lowDiagonalCorrectionInterval n (k + (j + 1))) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 2
        omega
      rw [hshift]
      simp only [Nat.add_zero]
      ring

private theorem lowDiagonalHeadInterval_width_eq (n K : ℕ) :
    width (lowDiagonalHeadInterval n K) =
      ∑ j ∈ Finset.range K,
        width (lowDiagonalCorrectionInterval n (1 + j)) := by
  unfold lowDiagonalHeadInterval
  rw [lowDiagonalHeadIntervalAux_width_eq, width_pure]
  simp

private theorem lowExactCheckpointHead_width_eq (n total used : ℕ) :
    width (lowExactCheckpointHead n total used) =
      ∑ i ∈ Finset.range used,
        width (lowScheduledChunkInterval n total i) := by
  apply width_recursive_add_eq_sum
  · rfl
  · intro i
    rfl

private theorem lowRoundedChunk_width_le
    (n total i : ℕ) {scale : ℚ} (hscale : 0 < scale) :
    width (lowRoundedChunkBox n total scale i) ≤
      width (lowScheduledChunkInterval n total i) + 2 / scale := by
  simpa only [lowRoundedChunkBox,
    YoshidaSineCheckpointedHead.outwardRoundedInterval,
    RatInterval.outwardRoundedInterval] using
      RatInterval.width_outwardRoundedInterval_le hscale
        (lowScheduledChunkInterval n total i)

private theorem lowDiagonalBlocks_le (n : ℕ) :
    lowDiagonalBlocks n ≤ 128 := by
  unfold lowDiagonalBlocks
  split_ifs <;> norm_num

private theorem lowDiagonalCutoff_le (n : ℕ) :
    256 * lowDiagonalBlocks n ≤ 32768 := by
  have h := lowDiagonalBlocks_le n
  omega

private theorem harmonic_le_twelve {N : ℕ} (hN : N ≤ 32768) :
    harmonic N ≤ 12 := by
  by_cases hN0 : N = 0
  · subst N
    norm_num [harmonic]
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero hN0
  have hcast : (N : ℝ) ≤ 32768 := by exact_mod_cast hN
  have hlogMono : Real.log (N : ℝ) ≤ Real.log 32768 :=
    Real.log_le_log hNpos hcast
  have hlogPow : Real.log (32768 : ℝ) = 15 * Real.log 2 := by
    rw [show (32768 : ℝ) = 2 ^ 15 by norm_num, Real.log_pow]
    norm_num
  have hlogTwo : Real.log 2 ≤ (7 / 10 : ℝ) := by
    have h := lowLogTwoInterval_contains.2
    unfold YoshidaOddGramPrefix.yoshidaLength at h
    norm_num [lowLogTwoInterval, factorTwoPrimeLogTwoInterval] at h ⊢
    linarith
  have hh := harmonic_le_one_add_log N
  have hh12 : ((harmonic N : ℚ) : ℝ) ≤ 12 := by
    calc
      ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log (N : ℝ) := hh
      _ ≤ 1 + Real.log 32768 := by linarith
      _ = 1 + 15 * Real.log 2 := by rw [hlogPow]
      _ ≤ 12 := by nlinarith
  exact_mod_cast hh12

private theorem lowDiagonalHead_width_le_harmonic (n K : ℕ) :
    width (lowDiagonalHeadInterval n K) ≤
      (1 / 50000000000 : ℚ) * harmonic K := by
  rw [lowDiagonalHeadInterval_width_eq, harmonic]
  calc
    (∑ j ∈ Finset.range K,
        width (lowDiagonalCorrectionInterval n (1 + j))) ≤
        ∑ j ∈ Finset.range K,
          1 / (50000000000 * ((1 + j : ℕ) : ℚ)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact lowDiagonalCorrection_width_le n (1 + j) (by omega)
    _ = (1 / 50000000000 : ℚ) *
        ∑ j ∈ Finset.range K, ((j + 1 : ℕ) : ℚ)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      norm_num [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = (1 / 50000000000 : ℚ) *
        ∑ j ∈ Finset.range K, ((j + 1 : ℕ) : ℚ)⁻¹ := rfl

private theorem lowRoundedHead_width_le (n : ℕ) :
    (∑ i ∈ Finset.range (lowDiagonalBlocks n),
        width (lowRoundedChunkBox n (lowDiagonalBlocks n)
          lowDiagonalRoundingScale i)) ≤
      (241 / 1000000000000 : ℚ) := by
  let blocks := lowDiagonalBlocks n
  let N := 256 * blocks
  have hblocks : 0 < blocks := by
    dsimp only [blocks]
    exact lowDiagonalBlocks_pos n
  have hround :
      (∑ i ∈ Finset.range blocks,
          width (lowRoundedChunkBox n blocks lowDiagonalRoundingScale i)) ≤
        (∑ i ∈ Finset.range blocks,
          width (lowScheduledChunkInterval n blocks i)) +
            (blocks : ℚ) * (2 / lowDiagonalRoundingScale) := by
    calc
      (∑ i ∈ Finset.range blocks,
          width (lowRoundedChunkBox n blocks lowDiagonalRoundingScale i)) ≤
          ∑ i ∈ Finset.range blocks,
            (width (lowScheduledChunkInterval n blocks i) +
              2 / lowDiagonalRoundingScale) := by
        apply Finset.sum_le_sum
        intro i _
        exact lowRoundedChunk_width_le n blocks i (by
          norm_num [lowDiagonalRoundingScale])
      _ = (∑ i ∈ Finset.range blocks,
          width (lowScheduledChunkInterval n blocks i)) +
            (blocks : ℚ) * (2 / lowDiagonalRoundingScale) := by
        rw [Finset.sum_add_distrib]
        simp
  have hExact :
      (∑ i ∈ Finset.range blocks,
          width (lowScheduledChunkInterval n blocks i)) =
        width (lowDiagonalHeadInterval n (N - 1)) := by
    rw [← lowExactCheckpointHead_width_eq n blocks blocks,
      lowExactCheckpointHead_eq_diagonalHead n blocks hblocks]
  have hN : N ≤ 32768 := by
    dsimp only [N]
    have hb : blocks ≤ 128 := by
      dsimp only [blocks]
      exact lowDiagonalBlocks_le n
    omega
  have hhead : width (lowDiagonalHeadInterval n (N - 1)) ≤
      (12 / 50000000000 : ℚ) := by
    calc
      width (lowDiagonalHeadInterval n (N - 1)) ≤
          (1 / 50000000000 : ℚ) * harmonic (N - 1) :=
        lowDiagonalHead_width_le_harmonic n (N - 1)
      _ ≤ (1 / 50000000000 : ℚ) * 12 := by
        gcongr
        exact harmonic_le_twelve (by omega)
      _ = 12 / 50000000000 := by ring
  rw [hExact] at hround
  have hbQ : (blocks : ℚ) ≤ 128 := by
    exact_mod_cast (show blocks ≤ 128 by
      dsimp only [blocks]
      exact lowDiagonalBlocks_le n)
  calc
    (∑ i ∈ Finset.range blocks,
        width (lowRoundedChunkBox n blocks lowDiagonalRoundingScale i)) ≤
      width (lowDiagonalHeadInterval n (N - 1)) +
        (blocks : ℚ) * (2 / lowDiagonalRoundingScale) := hround
    _ ≤ (12 / 50000000000 : ℚ) +
        128 * (2 / lowDiagonalRoundingScale) := by
      exact add_le_add hhead (mul_le_mul_of_nonneg_right hbQ (by
        norm_num [lowDiagonalRoundingScale]))
    _ ≤ 241 / 1000000000000 := by
      norm_num [lowDiagonalRoundingScale]

private theorem lowDiagonalRamp_base_metrics (n : ℕ) :
    LowIntervalMetrics
      (lowDiagonalRampInterval n (-1 / 2) sqrtTwoInterval)
      60 (6 / 100000000000) := by
  let m : ℚ := (n : ℚ) ^ 2
  let x : ℚ := 1 / 4
  let t : ℚ := x + 64 * m
  have hm0 : 0 ≤ m := by dsimp only [m]; positivity
  have hx0 : 0 < x := by dsimp only [x]; norm_num
  have ht0 : 0 < t := by dsimp only [t]; positivity
  have hp : LowIntervalMetrics (lowKappaSqInterval n) (100 * m)
      (m / 100000000000) := by
    simpa only [m] using lowKappaSq_metrics n
  have hhalf := lowMetrics_pure (q := (-1 / 2 : ℚ)) (B := 1 / 2)
    (by norm_num) (by norm_num)
  have hxI := lowMetrics_pure (q := x) (B := x)
    (by rw [abs_of_pos hx0]) hx0.le
  have hone := lowMetrics_pure (q := (1 : ℚ)) (B := 1)
    (by norm_num) (by norm_num)
  have htwo := lowMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have hshift := lowMetrics_add (lowMetrics_sub lowSqrtTwo_metrics hone)
    (lowMetrics_mul hhalf lowLogTwo_metrics)
  have hdiff := lowMetrics_sub hxI hp
  have htermOne := lowMetrics_mul hshift hdiff
  have htermTwo := lowMetrics_mul
    (lowMetrics_mul (lowMetrics_mul htwo hhalf) hp) lowLogTwo_metrics
  have hnum := lowMetrics_add htermOne htermTwo
  have hnum' : LowIntervalMetrics
      (((sqrtTwoInterval - RatInterval.pure 1 +
          RatInterval.pure (-1 / 2) * lowLogTwoInterval) *
          (RatInterval.pure x - lowKappaSqInterval n) +
        RatInterval.pure 2 * RatInterval.pure (-1 / 2) *
          lowKappaSqInterval n * lowLogTwoInterval))
      (10 * t) (7 * t / 10000000000000) := by
    apply hnum.weaken
    · dsimp only [t, x]
      norm_num
      nlinarith
    · dsimp only [t, x]
      norm_num
      nlinarith
  have hsum := lowMetrics_add hxI hp
  have hsum0 : 0 ≤
      (RatInterval.pure x + lowKappaSqInterval n).lower := by
    change 0 ≤ x + (lowKappaSqInterval n).lower
    exact add_nonneg hx0.le (lowKappaSqInterval_lower_nonneg n)
  have hsq := lowMetrics_positiveSquare hsum hsum0
  have hden := lowMetrics_mul lowLogTwo_metrics hsq
  have hden' : LowIntervalMetrics
      (lowLogTwoInterval *
        lowPositiveSquare (RatInterval.pure x + lowKappaSqInterval n))
      ((x + 100 * m) ^ 2) (6 * t ^ 2 / 10000000000000) := by
    exact hden.weaken (by norm_num) (by
      dsimp only [t]
      have hnonnegOne : 0 ≤ 59 * x ^ 2 := by positivity
      have hnonnegTwo : 0 ≤ 5480 * x * m := by positivity
      have hnonnegThree : 0 ≤ 35760 * m ^ 2 := by positivity
      norm_num
      nlinarith)
  let d : ℚ := (2 / 3) * t ^ 2
  have hd0 : 0 < d := by dsimp only [d]; positivity
  have hsumLower : t ≤
      (RatInterval.pure x + lowKappaSqInterval n).lower := by
    change x + 64 * m ≤ x + (lowKappaSqInterval n).lower
    have hpLower := lowKappaSq_lower n
    simpa only [m, add_comm] using add_le_add_left hpLower x
  have hsumUpper : t ≤
      (RatInterval.pure x + lowKappaSqInterval n).upper :=
    hsumLower.trans hsum.valid
  have hsquareLower : t ^ 2 ≤
      (lowPositiveSquare
        (RatInterval.pure x + lowKappaSqInterval n)).lower :=
    pow_le_pow_left₀ ht0.le hsumLower 2
  have hsquareUpper : t ^ 2 ≤
      (lowPositiveSquare
        (RatInterval.pure x + lowKappaSqInterval n)).upper :=
    pow_le_pow_left₀ ht0.le hsumUpper 2
  have hLupper : (2 / 3 : ℚ) ≤ lowLogTwoInterval.upper :=
    lowLogTwo_lower.trans lowLogTwo_metrics.valid
  have hLlower0 : (0 : ℚ) ≤ lowLogTwoInterval.lower :=
    (by norm_num : (0 : ℚ) ≤ 2 / 3).trans lowLogTwo_lower
  have hLupper0 : (0 : ℚ) ≤ lowLogTwoInterval.upper :=
    hLlower0.trans lowLogTwo_metrics.valid
  have hdenLower : d ≤
      (lowLogTwoInterval * lowPositiveSquare
        (RatInterval.pure x + lowKappaSqInterval n)).lower := by
    change d ≤ min
      (min (lowLogTwoInterval.lower *
          (lowPositiveSquare
            (RatInterval.pure x + lowKappaSqInterval n)).lower)
        (lowLogTwoInterval.lower *
          (lowPositiveSquare
            (RatInterval.pure x + lowKappaSqInterval n)).upper))
      (min (lowLogTwoInterval.upper *
          (lowPositiveSquare
            (RatInterval.pure x + lowKappaSqInterval n)).lower)
        (lowLogTwoInterval.upper *
          (lowPositiveSquare
            (RatInterval.pure x + lowKappaSqInterval n)).upper))
    dsimp only [d]
    apply le_min <;> apply le_min
    · exact mul_le_mul lowLogTwo_lower hsquareLower (sq_nonneg t) hLlower0
    · exact mul_le_mul lowLogTwo_lower hsquareUpper (sq_nonneg t) hLlower0
    · exact mul_le_mul hLupper hsquareLower (sq_nonneg t) hLupper0
    · exact mul_le_mul hLupper hsquareUpper (sq_nonneg t) hLupper0
  have hquot := lowMetrics_div hnum' hden' hd0 hdenLower
  have htQuarter : (1 / 4 : ℚ) ≤ t := by
    dsimp only [t, x]
    nlinarith
  have hquot' := hquot.weaken (B' := 60)
    (W' := 6 / 100000000000) (by
      dsimp only [d]
      field_simp [ht0.ne']
      nlinarith) (by
      dsimp only [d]
      field_simp [ht0.ne']
      nlinarith)
  have hxsq : (-1 / 2 : ℚ) ^ 2 = x := by
    dsimp only [x]
    norm_num
  simpa only [lowDiagonalRampInterval, m, x, t, hxsq] using hquot'

private theorem lowLogPi_width_le :
    width lowLogPiInterval ≤ (1 / 1000000000000 : ℚ) := by
  norm_num [lowLogPiInterval, lowLogPiXLower, lowLogPiXUpper,
    logRatioLower, logRatioUpper, piFineInterval, width,
    Finset.sum_range_succ]

private theorem lowLogFourThirds_width_le :
    width lowLogFourThirdsInterval ≤ (1 / 1000000000000 : ℚ) := by
  norm_num [lowLogFourThirdsInterval, logRatioInterval, logRatioLower,
    logRatioUpper, width, Finset.sum_range_succ]

private theorem lowPiFine_metrics :
    LowIntervalMetrics piFineInterval 4 (1 / 100000000000000000000) := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
    norm_num [piFineInterval, RatInterval.Valid, AbsBound, width]

private theorem lowBasePiTerm_width_le :
    width (lowDiagonalAInterval * positiveSquare piFineInterval / pure 6) ≤
      (1 / 1000000000000 : ℚ) := by
  have hpiSqLocal := lowMetrics_positiveSquare lowPiFine_metrics (by
    norm_num [piFineInterval])
  have hpiSq : LowIntervalMetrics (positiveSquare piFineInterval) 16
      (8 / 100000000000000000000) := by
    norm_num at hpiSqLocal ⊢
    simpa only [positiveSquare, lowPositiveSquare] using hpiSqLocal
  have hnum := lowMetrics_mul lowDiagonalA_metrics hpiSq
  have hsix := lowMetrics_pure (q := (6 : ℚ)) (B := 6)
    (by norm_num) (by norm_num)
  have hquot := lowMetrics_div hnum hsix (by norm_num : (0 : ℚ) < 6)
    (by simp [RatInterval.pure])
  exact hquot.width_le.trans (by norm_num)

private theorem lowDiagonalBase_width_le (n : ℕ) :
    width (lowDiagonalBaseInterval n) ≤ (15 / 100000000000 : ℚ) := by
  have hramp := lowDiagonalRamp_base_metrics n
  have htwo := lowMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have htworamp := lowMetrics_mul htwo hramp
  unfold lowDiagonalBaseInterval
  rw [width_add, width_add, width_sub, width_sub]
  calc
    width (pure 2 * lowDiagonalRampInterval n (-1 / 2) sqrtTwoInterval) +
          width eulerGammaUltraFineInterval + width lowLogPiInterval +
        width lowLogFourThirdsInterval +
          width (lowDiagonalAInterval * positiveSquare piFineInterval /
            pure 6) ≤
        (12 / 100000000000 : ℚ) + 1 / 1000000000000 +
          1 / 1000000000000 + 1 / 1000000000000 +
          1 / 1000000000000 := by
      have hrampWidth : width
          (pure 2 * lowDiagonalRampInterval n (-1 / 2) sqrtTwoInterval) ≤
          (12 / 100000000000 : ℚ) :=
        htworamp.width_le.trans (by norm_num)
      linarith [hrampWidth, eulerGammaUltraFineInterval_width_le,
        lowLogPi_width_le, lowLogFourThirds_width_le,
        lowBasePiTerm_width_le]
    _ ≤ 15 / 100000000000 := by norm_num

private theorem lowDiagonalCutoff_ge_390_mode
    {n : ℕ} (hn59 : n ≤ 59) :
    390 * n ≤ 256 * lowDiagonalBlocks n := by
  unfold lowDiagonalBlocks
  split_ifs <;> omega

private theorem lowDiagonalCutoff_ge_512 (n : ℕ) :
    512 ≤ 256 * lowDiagonalBlocks n := by
  unfold lowDiagonalBlocks
  split_ifs <;> norm_num

private theorem lowDiagonalCutoff_ge_1024_of_ne_zero
    {n : ℕ} (hn0 : n ≠ 0) :
    1024 ≤ 256 * lowDiagonalBlocks n := by
  unfold lowDiagonalBlocks
  split_ifs <;> omega

private theorem lowTailP_metrics
    {n : ℕ} (hn59 : n ≤ 59) :
    let N : ℚ := 256 * lowDiagonalBlocks n
    LowIntervalMetrics (lowKappaSqInterval n + pure 1)
      (N ^ 2 / 1800) (N ^ 2 / 10000000000000000) := by
  let Nn : ℕ := 256 * lowDiagonalBlocks n
  let N : ℚ := 256 * (lowDiagonalBlocks n : ℚ)
  dsimp only
  change LowIntervalMetrics (lowKappaSqInterval n + pure 1)
    (N ^ 2 / 1800) (N ^ 2 / 10000000000000000)
  have hN390Nat : 390 * n ≤ Nn := by
    dsimp only [Nn]
    exact lowDiagonalCutoff_ge_390_mode hn59
  have hN390 : (390 : ℚ) * n ≤ N := by
    dsimp only [N, Nn] at hN390Nat ⊢
    exact_mod_cast hN390Nat
  have hn0q : (0 : ℚ) ≤ n := by positivity
  have hN0 : (0 : ℚ) ≤ N := by positivity
  have hsq390 : (390 * (n : ℚ)) ^ 2 ≤ N ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hn0q) hN390 2
  have hp := lowKappaSq_metrics_sharp n
  have hone := lowMetrics_pure (q := (1 : ℚ)) (B := 1)
    (by norm_num) (by norm_num)
  have hP := lowMetrics_add hp hone
  apply hP.weaken
  · have hbound :
        1800 * (84 * (n : ℚ) ^ 2 + 1) ≤ N ^ 2 := by
      by_cases hn0 : n = 0
      · subst n
        norm_num [N, Nn, lowDiagonalBlocks]
      by_cases hn1 : n = 1
      · subst n
        norm_num [N, Nn, lowDiagonalBlocks]
      have hn2 : (2 : ℚ) ≤ n := by
        exact_mod_cast (show 2 ≤ n by omega)
      nlinarith [sq_nonneg (n : ℚ)]
    rw [le_div_iff₀ (by norm_num : (0 : ℚ) < 1800)]
    simpa only [mul_comm] using hbound
  · norm_num
    nlinarith [sq_nonneg (n : ℚ)]

private theorem lowHigherResidual_upper_le
    {n : ℕ} (hn59 : n ≤ 59) :
    let N := 256 * lowDiagonalBlocks n
    (lowHigherResidualRadiusInterval n N).upper ≤
      (53 / 200000000000 : ℚ) := by
  by_cases hn0 : n = 0
  · subst n
    change (lowHigherResidualRadiusInterval 0 512).upper ≤
      (53 / 200000000000 : ℚ)
    let N : ℚ := 512
    have hp : LowIntervalMetrics (lowKappaSqInterval 0) 0 0 := by
      simpa using lowKappaSq_metrics_sharp 0
    have hone := lowMetrics_pure (q := (1 : ℚ)) (B := 1)
      (by norm_num) (by norm_num)
    have htwo := lowMetrics_pure (q := (2 : ℚ)) (B := 2)
      (by norm_num) (by norm_num)
    have hP := lowMetrics_add hp hone
    have hP2 := lowMetrics_mul hP hP
    have hP3 := lowMetrics_mul hP2 hP
    have hP4 := lowMetrics_mul hP3 hP
    have hN2 := lowMetrics_pure (q := N ^ 2) (B := N ^ 2)
      (by dsimp only [N]; norm_num) (by positivity)
    have hN3 := lowMetrics_pure (q := N ^ 3) (B := N ^ 3)
      (by dsimp only [N]; norm_num) (by positivity)
    have hN4 := lowMetrics_pure (q := N ^ 4) (B := N ^ 4)
      (by dsimp only [N]; norm_num) (by positivity)
    have hN5 := lowMetrics_pure (q := N ^ 5) (B := N ^ 5)
      (by dsimp only [N]; norm_num) (by positivity)
    have hN6 := lowMetrics_pure (q := N ^ 6) (B := N ^ 6)
      (by dsimp only [N]; norm_num) (by positivity)
    have hterm3 := lowMetrics_div hP2 hN3 (by positivity : 0 < N ^ 3)
      (by simp [RatInterval.pure])
    have hterm4 := lowMetrics_div hP3 hN4 (by positivity : 0 < N ^ 4)
      (by simp [RatInterval.pure])
    have hterm5 := lowMetrics_div hP3 hN5 (by positivity : 0 < N ^ 5)
      (by simp [RatInterval.pure])
    have hterm6 := lowMetrics_div (lowMetrics_add hP4 htwo) hN6
      (by positivity : 0 < N ^ 6) (by simp [RatInterval.pure])
    have hscaleRaw := lowMetrics_add
      (lowMetrics_add (lowMetrics_add hterm3 hterm4) hterm5) hterm6
    have hscale : LowIntervalMetrics (lowHigherTailScaleInterval 0 512)
        ((N ^ 3)⁻¹ + (N ^ 4)⁻¹ + (N ^ 5)⁻¹ +
          (1 + 2) * (N ^ 6)⁻¹) 0 := by
      simpa [lowHigherTailScaleInterval, N] using hscaleRaw
    have heleven := lowMetrics_pure (q := (11 : ℚ)) (B := 11)
      (by norm_num) (by norm_num)
    have htwenty := lowMetrics_pure (q := (20 : ℚ)) (B := 20)
      (by norm_num) (by norm_num)
    have hden := lowMetrics_mul htwenty hN2
    have hres := lowMetrics_div (lowMetrics_mul heleven hscale) hden
      (by positivity : 0 < 20 * N ^ 2) (by
        change 20 * N ^ 2 ≤ min (min (20 * N ^ 2) (20 * N ^ 2))
          (min (20 * N ^ 2) (20 * N ^ 2))
        simp)
    unfold lowHigherResidualRadiusInterval
    exact hres.absBound.2.trans (by
      dsimp only [N]
      norm_num)
  dsimp only
  let Nn : ℕ := 256 * lowDiagonalBlocks n
  let N : ℚ := 256 * (lowDiagonalBlocks n : ℚ)
  have hN1024Nat : 1024 ≤ Nn := by
    dsimp only [Nn]
    exact lowDiagonalCutoff_ge_1024_of_ne_zero hn0
  have hN1024 : (1024 : ℚ) ≤ N := by
    dsimp only [N, Nn] at hN1024Nat ⊢
    exact_mod_cast hN1024Nat
  have hN0 : 0 < N := (by norm_num : (0 : ℚ) < 1024).trans_le hN1024
  have hP : LowIntervalMetrics
      (lowKappaSqInterval n + RatInterval.pure 1)
      (N ^ 2 / 1800) (N ^ 2 / 10000000000000000) := by
    simpa only [N] using lowTailP_metrics hn59
  have hP2 := lowMetrics_mul hP hP
  have hP3 := lowMetrics_mul hP2 hP
  have hP4 := lowMetrics_mul hP3 hP
  have hN3 := lowMetrics_pure (q := N ^ 3) (B := N ^ 3)
    (by rw [abs_of_pos (by positivity : 0 < N ^ 3)]) (by positivity)
  have hN4 := lowMetrics_pure (q := N ^ 4) (B := N ^ 4)
    (by rw [abs_of_pos (by positivity : 0 < N ^ 4)]) (by positivity)
  have hN5 := lowMetrics_pure (q := N ^ 5) (B := N ^ 5)
    (by rw [abs_of_pos (by positivity : 0 < N ^ 5)]) (by positivity)
  have hN6 := lowMetrics_pure (q := N ^ 6) (B := N ^ 6)
    (by rw [abs_of_pos (by positivity : 0 < N ^ 6)]) (by positivity)
  have htwo := lowMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have hterm3 := lowMetrics_div hP2 hN3 (by positivity : 0 < N ^ 3)
    (by simp [RatInterval.pure])
  have hterm4 := lowMetrics_div hP3 hN4 (by positivity : 0 < N ^ 4)
    (by simp [RatInterval.pure])
  have hterm5 := lowMetrics_div hP3 hN5 (by positivity : 0 < N ^ 5)
    (by simp [RatInterval.pure])
  have hterm6 := lowMetrics_div (lowMetrics_add hP4 htwo) hN6
    (by positivity : 0 < N ^ 6) (by simp [RatInterval.pure])
  have hscale := lowMetrics_add (lowMetrics_add (lowMetrics_add hterm3 hterm4)
    hterm5) hterm6
  let SB : ℚ :=
    N / 1800 ^ 2 + N ^ 2 / 1800 ^ 3 + N / 1800 ^ 3 +
      N ^ 2 / 1800 ^ 4 + 2 / N ^ 6
  have hcast : (Nn : ℚ) = N := by
    dsimp only [Nn, N]
    norm_num
  have hscaleValid : (lowHigherTailScaleInterval n Nn).Valid := by
    unfold lowHigherTailScaleInterval
    dsimp only
    rw [hcast]
    exact hscale.valid
  have hscaleAbs : (lowHigherTailScaleInterval n Nn).AbsBound SB := by
    unfold lowHigherTailScaleInterval
    dsimp only
    rw [hcast]
    have hraw := hscale.absBound
    convert hraw using 1
    dsimp only [SB]
    field_simp [hN0.ne']
    ring
  have hSB0 : 0 ≤ SB := by
    dsimp only [SB]
    positivity
  have heleven := lowMetrics_pure (q := (11 : ℚ)) (B := 11)
    (by norm_num) (by norm_num)
  have htwenty := lowMetrics_pure (q := (20 : ℚ)) (B := 20)
    (by norm_num) (by norm_num)
  have hN2 := lowMetrics_pure (q := N ^ 2) (B := N ^ 2)
    (by rw [abs_of_pos (by positivity : 0 < N ^ 2)]) (by positivity)
  have hden := lowMetrics_mul htwenty hN2
  have hdenLower : 20 * N ^ 2 ≤
      (RatInterval.pure 20 * RatInterval.pure (N ^ 2)).lower := by
    change 20 * N ^ 2 ≤ min (min (20 * N ^ 2) (20 * N ^ 2))
      (min (20 * N ^ 2) (20 * N ^ 2))
    simp
  have hnumValid := valid_mul heleven.valid hscaleValid
  have hnumAbs :
      (RatInterval.pure 11 * lowHigherTailScaleInterval n Nn).AbsBound
        (11 * SB) :=
    absBound_mul heleven.valid hscaleValid heleven.absBound hscaleAbs
      (by norm_num) hSB0
  have hresAbs := absBound_div_of_lower hnumValid hden.valid hnumAbs
    (mul_nonneg (by norm_num) hSB0)
    (by positivity : 0 < 20 * N ^ 2) hdenLower
  have hresUpper := hresAbs.2
  have hInv : 1 / N ≤ (1 / 1024 : ℚ) :=
    one_div_le_one_div_of_le (by norm_num) hN1024
  have hN8 : (1024 : ℚ) ^ 8 ≤ N ^ 8 :=
    pow_le_pow_left₀ (by norm_num) hN1024 8
  have hInv8 : 1 / N ^ 8 ≤ (1 / 1024 ^ 8 : ℚ) :=
    one_div_le_one_div_of_le (by positivity) hN8
  have hnumeric : 11 * SB * (20 * N ^ 2)⁻¹ ≤
      (53 / 200000000000 : ℚ) := by
    have heq : 11 * SB * (20 * N ^ 2)⁻¹ =
        (11 / 20) *
          (1 / (1800 ^ 2 * N) + 1 / 1800 ^ 3 +
            1 / (1800 ^ 3 * N) + 1 / 1800 ^ 4 + 2 / N ^ 8) := by
      dsimp only [SB]
      field_simp [hN0.ne']
    rw [heq]
    calc
      (11 / 20 : ℚ) *
          (1 / (1800 ^ 2 * N) + 1 / 1800 ^ 3 +
            1 / (1800 ^ 3 * N) + 1 / 1800 ^ 4 + 2 / N ^ 8) ≤
          (11 / 20 : ℚ) *
            (1 / (1800 ^ 2 * 1024) + 1 / 1800 ^ 3 +
              1 / (1800 ^ 3 * 1024) + 1 / 1800 ^ 4 +
                2 / 1024 ^ 8) := by
        gcongr
      _ ≤ 53 / 200000000000 := by norm_num
  unfold lowHigherResidualRadiusInterval
  rw [show (256 * lowDiagonalBlocks n : ℕ) = Nn by rfl]
  change (RatInterval.pure 11 * lowHigherTailScaleInterval n Nn /
    (RatInterval.pure 20 * RatInterval.pure ((Nn : ℚ) ^ 2))).upper ≤ _
  have hmetricUpper :
      (RatInterval.pure 11 * lowHigherTailScaleInterval n Nn /
        (RatInterval.pure 20 * RatInterval.pure ((Nn : ℚ) ^ 2))).upper ≤
          11 * SB * (20 * N ^ 2)⁻¹ := by
    simpa only [hcast] using hresUpper
  exact hmetricUpper.trans hnumeric

private theorem lowTailKappa_metrics
    {n : ℕ} (hn59 : n ≤ 59) :
    let N : ℚ := 256 * lowDiagonalBlocks n
    LowIntervalMetrics (lowKappaSqInterval n) (N ^ 2)
      (N ^ 2 / 10000000000000) := by
  let N : ℚ := 256 * (lowDiagonalBlocks n : ℚ)
  dsimp only
  change LowIntervalMetrics (lowKappaSqInterval n) (N ^ 2)
    (N ^ 2 / 10000000000000)
  have hN390Nat := lowDiagonalCutoff_ge_390_mode hn59
  have hN390 : (390 : ℚ) * n ≤ N := by
    dsimp only [N]
    exact_mod_cast hN390Nat
  have hn0 : (0 : ℚ) ≤ n := by positivity
  have hsq : (390 * (n : ℚ)) ^ 2 ≤ N ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by norm_num) hn0) hN390 2
  apply (lowKappaSq_metrics_sharp n).weaken
  · nlinarith [sq_nonneg (n : ℚ)]
  · nlinarith [sq_nonneg (n : ℚ)]

private theorem lowCoeffDenom_lower_bound {c : ℚ} (hc : 0 ≤ c) :
    (2 * c / 3 : ℚ) ≤
      (RatInterval.pure c * lowLogTwoInterval).lower := by
  have hLu : (2 / 3 : ℚ) ≤ lowLogTwoInterval.upper :=
    lowLogTwo_lower.trans lowLogTwo_metrics.valid
  change 2 * c / 3 ≤ min
    (min (c * lowLogTwoInterval.lower) (c * lowLogTwoInterval.upper))
    (min (c * lowLogTwoInterval.lower) (c * lowLogTwoInterval.upper))
  apply le_min <;> apply le_min
  · nlinarith [mul_le_mul_of_nonneg_left lowLogTwo_lower hc]
  · nlinarith [mul_le_mul_of_nonneg_left hLu hc]
  · nlinarith [mul_le_mul_of_nonneg_left lowLogTwo_lower hc]
  · nlinarith [mul_le_mul_of_nonneg_left hLu hc]

private theorem lowInvPowTail_three_metrics
    {N : ℕ} (hN : 1 ≤ N) :
    LowIntervalMetrics (lowInvPowTailInterval N 3)
      (2 / (N : ℚ) ^ 2) (1 / (12 * (N : ℚ) ^ 6)) := by
  have hNq : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℚ) < N := lt_of_lt_of_le (by norm_num) hNq
  refine ⟨?_, ?_, ?_, by positivity, by positivity⟩
  · norm_num [RatInterval.Valid, lowInvPowTailInterval, lowInvPowLowerQ,
      lowInvPowUpperQ]
  · unfold RatInterval.AbsBound
    constructor
    · norm_num [lowInvPowTailInterval, lowInvPowLowerQ, lowInvPowUpperQ]
      field_simp [hNpos.ne']
      calc
        (2 : ℚ) * 4 ≤ 12 * 1 ^ 2 * 2 := by norm_num
        _ ≤ 12 * (N : ℚ) ^ 2 *
            ((N : ℚ) * ((N : ℚ) + 1) * 4 + 2 +
              (N : ℚ) ^ 2 * 2 ^ 2 * 4) := by
          gcongr
          nlinarith [mul_nonneg
            (mul_nonneg (show (0 : ℚ) ≤ N by positivity)
              (show (0 : ℚ) ≤ (N : ℚ) + 1 by positivity))
            (by norm_num : (0 : ℚ) ≤ 4)]
    · norm_num [lowInvPowTailInterval, lowInvPowUpperQ]
      field_simp [hNpos.ne']
      nlinarith [sq_nonneg ((N : ℚ) - 1), sq_nonneg ((N : ℚ) ^ 2)]
  · norm_num [width, lowInvPowTailInterval, lowInvPowLowerQ,
      lowInvPowUpperQ]
    rw [mul_comm]

private theorem lowInvPowTail_four_metrics
    {N : ℕ} (hN : 1 ≤ N) :
    LowIntervalMetrics (lowInvPowTailInterval N 4)
      (2 / (N : ℚ) ^ 3) (1 / (6 * (N : ℚ) ^ 7)) := by
  have hNq : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℚ) < N := lt_of_lt_of_le (by norm_num) hNq
  refine ⟨?_, ?_, ?_, by positivity, by positivity⟩
  · norm_num [RatInterval.Valid, lowInvPowTailInterval, lowInvPowLowerQ,
      lowInvPowUpperQ]
  · unfold RatInterval.AbsBound
    constructor
    · norm_num [lowInvPowTailInterval, lowInvPowLowerQ, lowInvPowUpperQ]
      field_simp [hNpos.ne']
      calc
        (3 : ℚ) * 2 ≤ 6 * 1 ^ 2 * 2 := by norm_num
        _ ≤ 6 * (N : ℚ) ^ 2 *
            ((N : ℚ) * ((N : ℚ) * 2 + 3) + 2 +
              (N : ℚ) ^ 2 * 3 * 2 ^ 2) := by
          gcongr
          nlinarith [mul_nonneg (show (0 : ℚ) ≤ N by positivity)
            (show (0 : ℚ) ≤ (N : ℚ) * 2 + 3 by positivity)]
    · norm_num [lowInvPowTailInterval, lowInvPowUpperQ]
      field_simp [hNpos.ne']
      nlinarith [sq_nonneg ((N : ℚ) - 1), sq_nonneg ((N : ℚ) ^ 2),
        sq_nonneg ((N : ℚ) ^ 3)]
  · norm_num [width, lowInvPowTailInterval, lowInvPowLowerQ,
      lowInvPowUpperQ]
    rw [mul_comm]

private theorem lowInvPowTail_five_metrics
    {N : ℕ} (hN : 1 ≤ N) :
    LowIntervalMetrics (lowInvPowTailInterval N 5)
      (2 / (N : ℚ) ^ 4) (7 / (24 * (N : ℚ) ^ 8)) := by
  have hNq : (1 : ℚ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℚ) < N := lt_of_lt_of_le (by norm_num) hNq
  refine ⟨?_, ?_, ?_, by positivity, by positivity⟩
  · norm_num [RatInterval.Valid, lowInvPowTailInterval, lowInvPowLowerQ,
      lowInvPowUpperQ]
  · unfold RatInterval.AbsBound
    constructor
    · norm_num [lowInvPowTailInterval, lowInvPowLowerQ, lowInvPowUpperQ]
      field_simp [hNpos.ne']
      calc
        (7 : ℚ) * 4 * 2 * 12 ≤ 24 * 1 ^ 2 * 40 := by norm_num
        _ ≤ 24 * (N : ℚ) ^ 2 *
            ((N : ℚ) * ((N : ℚ) * 2 + 4) * 12 +
              4 * 2 * 5 + (N : ℚ) ^ 2 * 4 * 2 ^ 2 * 12) := by
          gcongr
          nlinarith [mul_nonneg
            (mul_nonneg (show (0 : ℚ) ≤ N by positivity)
              (show (0 : ℚ) ≤ (N : ℚ) * 2 + 4 by positivity))
            (by norm_num : (0 : ℚ) ≤ 12)]
    · norm_num [lowInvPowTailInterval, lowInvPowUpperQ]
      field_simp [hNpos.ne']
      nlinarith [sq_nonneg ((N : ℚ) - 1), sq_nonneg ((N : ℚ) ^ 2),
        sq_nonneg ((N : ℚ) ^ 3), sq_nonneg ((N : ℚ) ^ 4)]
  · norm_num [width, lowInvPowTailInterval, lowInvPowLowerQ,
      lowInvPowUpperQ]
    field_simp [hNpos.ne']
    norm_num

private theorem lowCoreCoeffThree_tail_metrics
    {n : ℕ} (hn59 : n ≤ 59) :
    let N : ℚ := 256 * lowDiagonalBlocks n
    LowIntervalMetrics (lowCoreCoeffThreeInterval n) (N ^ 2)
      (N ^ 2 / 10000000000000) := by
  let N : ℚ := 256 * (lowDiagonalBlocks n : ℚ)
  dsimp only
  change LowIntervalMetrics (lowCoreCoeffThreeInterval n) (N ^ 2)
    (N ^ 2 / 10000000000000)
  have hN512Nat := lowDiagonalCutoff_ge_512 n
  have hN512 : (512 : ℚ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hN512Nat
  have hN0 : 0 < N := (by norm_num : (0 : ℚ) < 512).trans_le hN512
  have hp := lowTailKappa_metrics hn59
  have hzero := lowMetrics_pure (q := (0 : ℚ)) (B := 0)
    (by norm_num) (by norm_num)
  have hfour := lowMetrics_pure (q := (4 : ℚ)) (B := 4)
    (by norm_num) (by norm_num)
  have hprod := lowMetrics_mul (lowMetrics_mul hfour lowLogTwo_metrics) hp
  have hinner := lowMetrics_sub (lowMetrics_sub hprod lowLogTwo_metrics) hfour
  have hnum := lowMetrics_sub hzero hinner
  have hnum' : LowIntervalMetrics
      (pure 0 - (pure 4 * lowLogTwoInterval * lowKappaSqInterval n -
        lowLogTwoInterval - pure 4)) (5 * N ^ 2)
      (5 * N ^ 2 / 10000000000000) := by
    apply hnum.weaken <;> norm_num at hnum ⊢
    · nlinarith [sq_nonneg N]
    · nlinarith [sq_nonneg N]
  have h16 := lowMetrics_pure (q := (16 : ℚ)) (B := 16)
    (by norm_num) (by norm_num)
  have hden := lowMetrics_mul h16 lowLogTwo_metrics
  have hdenLower : (32 / 3 : ℚ) ≤
      (RatInterval.pure 16 * lowLogTwoInterval).lower :=
    by
      have h := lowCoeffDenom_lower_bound (c := 16) (by norm_num)
      linarith
  have hquot := lowMetrics_div hnum' hden (by norm_num : (0 : ℚ) < 32 / 3)
    hdenLower
  unfold lowCoreCoeffThreeInterval
  dsimp only
  apply hquot.weaken
  · norm_num
    nlinarith [sq_nonneg N]
  · norm_num
    nlinarith [sq_nonneg N]

private theorem lowCoreCoeffFour_tail_metrics
    {n : ℕ} (hn59 : n ≤ 59) :
    let N : ℚ := 256 * lowDiagonalBlocks n
    LowIntervalMetrics (lowCoreCoeffFourInterval n) (N ^ 2)
      (N ^ 2 / 5000000000000) := by
  let N : ℚ := 256 * (lowDiagonalBlocks n : ℚ)
  dsimp only
  change LowIntervalMetrics (lowCoreCoeffFourInterval n) (N ^ 2)
    (N ^ 2 / 5000000000000)
  have hN512 : (512 : ℚ) ≤ N := by
    dsimp only [N]
    exact_mod_cast lowDiagonalCutoff_ge_512 n
  have hp := lowTailKappa_metrics hn59
  have h12 := lowMetrics_pure (q := (12 : ℚ)) (B := 12)
    (by norm_num) (by norm_num)
  have h24 := lowMetrics_pure (q := (24 : ℚ)) (B := 24)
    (by norm_num) (by norm_num)
  have h6 := lowMetrics_pure (q := (6 : ℚ)) (B := 6)
    (by norm_num) (by norm_num)
  have hterm12 := lowMetrics_mul (lowMetrics_mul h12 lowLogTwo_metrics) hp
  have hterm24 := lowMetrics_mul h24 hp
  have hnum := lowMetrics_sub
    (lowMetrics_add (lowMetrics_sub hterm12 lowLogTwo_metrics) hterm24) h6
  have hnum' : LowIntervalMetrics
      (pure 12 * lowLogTwoInterval * lowKappaSqInterval n -
          lowLogTwoInterval + pure 24 * lowKappaSqInterval n - pure 6)
      (37 * N ^ 2) (4 * N ^ 2 / 1000000000000) := by
    apply hnum.weaken <;> norm_num at hnum ⊢ <;>
      nlinarith [sq_nonneg N]
  have h64 := lowMetrics_pure (q := (64 : ℚ)) (B := 64)
    (by norm_num) (by norm_num)
  have hden := lowMetrics_mul h64 lowLogTwo_metrics
  have hdenLower : (128 / 3 : ℚ) ≤
      (pure 64 * lowLogTwoInterval).lower := by
    have h := lowCoeffDenom_lower_bound (c := 64) (by norm_num)
    linarith
  have hquot := lowMetrics_div hnum' hden
    (by norm_num : (0 : ℚ) < 128 / 3) hdenLower
  unfold lowCoreCoeffFourInterval
  dsimp only
  apply hquot.weaken
  · norm_num
    nlinarith [sq_nonneg N]
  · norm_num
    nlinarith [sq_nonneg N]

private theorem lowCoreCoeffFive_tail_metrics
    {n : ℕ} (hn59 : n ≤ 59) :
    let N : ℚ := 256 * lowDiagonalBlocks n
    LowIntervalMetrics (lowCoreCoeffFiveInterval n) (N ^ 4)
      (N ^ 4 / 40000000000000) := by
  let N : ℚ := 256 * (lowDiagonalBlocks n : ℚ)
  dsimp only
  change LowIntervalMetrics (lowCoreCoeffFiveInterval n) (N ^ 4)
    (N ^ 4 / 40000000000000)
  have hN512 : (512 : ℚ) ≤ N := by
    dsimp only [N]
    exact_mod_cast lowDiagonalCutoff_ge_512 n
  have hN2large : (512 : ℚ) ^ 2 ≤ N ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hN512 2
  have hp := lowTailKappa_metrics hn59
  have hp2 := lowMetrics_mul hp hp
  have h16 := lowMetrics_pure (q := (16 : ℚ)) (B := 16)
    (by norm_num) (by norm_num)
  have h24 := lowMetrics_pure (q := (24 : ℚ)) (B := 24)
    (by norm_num) (by norm_num)
  have h96 := lowMetrics_pure (q := (96 : ℚ)) (B := 96)
    (by norm_num) (by norm_num)
  have h8 := lowMetrics_pure (q := (8 : ℚ)) (B := 8)
    (by norm_num) (by norm_num)
  have hterm16 := lowMetrics_mul (lowMetrics_mul h16 lowLogTwo_metrics) hp2
  have hterm24 := lowMetrics_mul (lowMetrics_mul h24 lowLogTwo_metrics) hp
  have hterm96 := lowMetrics_mul h96 hp
  have hnum := lowMetrics_add
    (lowMetrics_sub
      (lowMetrics_add (lowMetrics_sub hterm16 hterm24) lowLogTwo_metrics)
      hterm96) h8
  have hnum' : LowIntervalMetrics
      (pure 16 * lowLogTwoInterval *
          (lowKappaSqInterval n * lowKappaSqInterval n) -
        pure 24 * lowLogTwoInterval * lowKappaSqInterval n +
          lowLogTwoInterval - pure 96 * lowKappaSqInterval n + pure 8)
      (17 * N ^ 4) (4 * N ^ 4 / 1000000000000) := by
    apply hnum.weaken <;> norm_num at hnum ⊢
    · nlinarith [sq_nonneg (N ^ 2)]
    · nlinarith [sq_nonneg (N ^ 2)]
  have h256 := lowMetrics_pure (q := (256 : ℚ)) (B := 256)
    (by norm_num) (by norm_num)
  have hden := lowMetrics_mul h256 lowLogTwo_metrics
  have hdenLower : (512 / 3 : ℚ) ≤
      (pure 256 * lowLogTwoInterval).lower := by
    have h := lowCoeffDenom_lower_bound (c := 256) (by norm_num)
    linarith
  have hquot := lowMetrics_div hnum' hden
    (by norm_num : (0 : ℚ) < 512 / 3) hdenLower
  unfold lowCoreCoeffFiveInterval
  dsimp only
  apply hquot.weaken
  · norm_num
    nlinarith [sq_nonneg (N ^ 2)]
  · norm_num
    nlinarith [sq_nonneg (N ^ 2)]

private theorem lowHigherMainTail_width_le
    {n : ℕ} (hn59 : n ≤ 59) :
    let N := 256 * lowDiagonalBlocks n
    width (lowHigherMainTailInterval n N) ≤
      (1 / 100000000000 : ℚ) := by
  let Nn : ℕ := 256 * lowDiagonalBlocks n
  let N : ℚ := 256 * (lowDiagonalBlocks n : ℚ)
  dsimp only
  have hcast : (Nn : ℚ) = N := by
    dsimp only [Nn, N]
    norm_num
  have hN512Nat : 512 ≤ Nn := by
    dsimp only [Nn]
    exact lowDiagonalCutoff_ge_512 n
  have hN512 : (512 : ℚ) ≤ N := by
    rw [← hcast]
    exact_mod_cast hN512Nat
  have hN0 : (0 : ℚ) < N := (by norm_num : (0 : ℚ) < 512).trans_le hN512
  have hN1Nat : 1 ≤ Nn := by omega
  have hc3 : LowIntervalMetrics (lowCoreCoeffThreeInterval n) (N ^ 2)
      (N ^ 2 / 10000000000000) := by
    simpa only [N] using lowCoreCoeffThree_tail_metrics hn59
  have hc4 : LowIntervalMetrics (lowCoreCoeffFourInterval n) (N ^ 2)
      (N ^ 2 / 5000000000000) := by
    simpa only [N] using lowCoreCoeffFour_tail_metrics hn59
  have hc5 : LowIntervalMetrics (lowCoreCoeffFiveInterval n) (N ^ 4)
      (N ^ 4 / 40000000000000) := by
    simpa only [N] using lowCoreCoeffFive_tail_metrics hn59
  have ht3 : LowIntervalMetrics (lowInvPowTailInterval Nn 3)
      (2 / N ^ 2) (1 / (12 * N ^ 6)) := by
    simpa only [hcast] using lowInvPowTail_three_metrics hN1Nat
  have ht4 : LowIntervalMetrics (lowInvPowTailInterval Nn 4)
      (2 / N ^ 3) (1 / (6 * N ^ 7)) := by
    simpa only [hcast] using lowInvPowTail_four_metrics hN1Nat
  have ht5 : LowIntervalMetrics (lowInvPowTailInterval Nn 5)
      (2 / N ^ 4) (7 / (24 * N ^ 8)) := by
    simpa only [hcast] using lowInvPowTail_five_metrics hN1Nat
  have hmain := lowMetrics_add
    (lowMetrics_add (lowMetrics_mul hc3 ht3) (lowMetrics_mul hc4 ht4))
    (lowMetrics_mul hc5 ht5)
  have hw : width (lowHigherMainTailInterval n Nn) ≤
      (2 / N ^ 2) * (N ^ 2 / 10000000000000) +
          N ^ 2 * (1 / (12 * N ^ 6)) +
        ((2 / N ^ 3) * (N ^ 2 / 5000000000000) +
          N ^ 2 * (1 / (6 * N ^ 7))) +
      ((2 / N ^ 4) * (N ^ 4 / 40000000000000) +
        N ^ 4 * (7 / (24 * N ^ 8))) := by
    unfold lowHigherMainTailInterval
    exact hmain.width_le
  have hInv : 1 / N ≤ (1 / 512 : ℚ) :=
    one_div_le_one_div_of_le (by norm_num) hN512
  have hN4 : (512 : ℚ) ^ 4 ≤ N ^ 4 :=
    pow_le_pow_left₀ (by norm_num) hN512 4
  have hN5 : (512 : ℚ) ^ 5 ≤ N ^ 5 :=
    pow_le_pow_left₀ (by norm_num) hN512 5
  have hInv4 : 1 / N ^ 4 ≤ (1 / 512 ^ 4 : ℚ) :=
    one_div_le_one_div_of_le (by positivity) hN4
  have hInv5 : 1 / N ^ 5 ≤ (1 / 512 ^ 5 : ℚ) :=
    one_div_le_one_div_of_le (by positivity) hN5
  have heq :
      (2 / N ^ 2) * (N ^ 2 / 10000000000000) +
          N ^ 2 * (1 / (12 * N ^ 6)) +
        ((2 / N ^ 3) * (N ^ 2 / 5000000000000) +
          N ^ 2 * (1 / (6 * N ^ 7))) +
      ((2 / N ^ 4) * (N ^ 4 / 40000000000000) +
        N ^ 4 * (7 / (24 * N ^ 8))) =
        2 / 10000000000000 + (1 / 12) * (1 / N ^ 4) +
          (2 / 5000000000000) * (1 / N) +
          (1 / 6) * (1 / N ^ 5) + 1 / 20000000000000 +
          (7 / 24) * (1 / N ^ 4) := by
    field_simp [hN0.ne']
    ring
  rw [heq] at hw
  calc
    width (lowHigherMainTailInterval n Nn) ≤
        2 / 10000000000000 + (1 / 12) * (1 / N ^ 4) +
          (2 / 5000000000000) * (1 / N) +
          (1 / 6) * (1 / N ^ 5) + 1 / 20000000000000 +
          (7 / 24) * (1 / N ^ 4) := hw
    _ ≤ 2 / 10000000000000 + (1 / 12) * (1 / 512 ^ 4) +
          (2 / 5000000000000) * (1 / 512) +
          (1 / 6) * (1 / 512 ^ 5) + 1 / 20000000000000 +
          (7 / 24) * (1 / 512 ^ 4) := by gcongr
    _ ≤ 1 / 100000000000 := by norm_num

private theorem lowHigherTail_width_le
    {n : ℕ} (hn59 : n ≤ 59) :
    width (lowHigherTailInterval n (256 * lowDiagonalBlocks n)) ≤
      (54 / 100000000000 : ℚ) := by
  let N : ℕ := 256 * lowDiagonalBlocks n
  have hmain : width (lowHigherMainTailInterval n N) ≤
      (1 / 100000000000 : ℚ) := by
    simpa only [N] using lowHigherMainTail_width_le hn59
  have hres : (lowHigherResidualRadiusInterval n N).upper ≤
      (53 / 200000000000 : ℚ) := by
    simpa only [N] using lowHigherResidual_upper_le hn59
  unfold lowHigherTailInterval
  dsimp only
  rw [width_add]
  change width (lowHigherMainTailInterval n N) +
      ((lowHigherResidualRadiusInterval n N).upper -
        (-(lowHigherResidualRadiusInterval n N).upper)) ≤ _
  linarith

/-- Every target in the complementary low band contains the actual analytic
diagonal moment, including the structurally separate zero mode. -/
theorem yoshidaFactorTwoCleanLowDiagonalTarget_contains
    {n : ℕ} (hn59 : n ≤ 59) :
    (yoshidaFactorTwoCleanLowDiagonalTarget n).Contains
      (yoshidaDiagonalMoment n) := by
  let blocks := lowDiagonalBlocks n
  let N := 256 * blocks
  have hblocks : 0 < blocks := lowDiagonalBlocks_pos n
  have hN : 16 ≤ N := lowDiagonalCutoff_ge_sixteen n
  have hmode : 10 * n ≤ N := ten_mul_mode_le_lowDiagonalCutoff hn59
  have hbase := lowDiagonalBaseInterval_contains n
  have hheadExact := lowDiagonalHeadInterval_contains n (N - 1)
  have hheadSub := lowDiagonalHeadInterval_sub_rounded n blocks hblocks
    (show (0 : ℚ) < lowDiagonalRoundingScale by
      norm_num [lowDiagonalRoundingScale])
  have hhead :
      (coarseCheckpointHead
        (lowRoundedChunkBox n blocks lowDiagonalRoundingScale) blocks).Contains
          (∑ j ∈ Finset.range (N - 1),
            yoshidaDiagonalDyadicPairedCorrection n (1 + j)) := by
    have hNpred : N - 1 = 256 * blocks - 1 := rfl
    rw [hNpred] at hheadExact
    exact contains_of_subinterval hheadSub hheadExact
  have htail := lowHigherTailInterval_contains hN hmode
  have hidentity : yoshidaDiagonalMoment n =
      diagonalAcceleratedBase n -
        ∑' j : ℕ, yoshidaDiagonalDyadicPairedCorrection n (j + 1) := by
    by_cases hn : n = 0
    · subst n
      exact yoshidaDiagonalMoment_zero_eq_acceleratedSeries
    · exact yoshidaDiagonalMoment_eq_acceleratedSeries hn
  rw [hidentity]
  rw [← lowDiagonalCorrection_head_add_tail_eq_tsum hN hmode]
  unfold yoshidaFactorTwoCleanLowDiagonalTarget
  dsimp only [blocks, N]
  have hcombine := contains_sub (contains_sub hbase hhead) htail
  convert hcombine using 1
  ring

/-- Structural width certificate for every complementary low mode from `0`
through `59`. -/
theorem yoshidaFactorTwoCleanLowDiagonalTarget_width_le
    {n : ℕ} (hn59 : n ≤ 59) :
    width (yoshidaFactorTwoCleanLowDiagonalTarget n) ≤
      (1 / 1000000000 : ℚ) := by
  rw [lowDiagonalTarget_width_eq]
  have hbase := lowDiagonalBase_width_le n
  have hhead := lowRoundedHead_width_le n
  have htail := lowHigherTail_width_le hn59
  linarith

/-- Complete containment and width obligation for the complementary low band. -/
def YoshidaFactorTwoCleanLowDiagonalTargetEnclosures : Prop :=
  ∀ n, n ≤ 59 →
    (yoshidaFactorTwoCleanLowDiagonalTarget n).Contains
        (yoshidaDiagonalMoment n) ∧
      width (yoshidaFactorTwoCleanLowDiagonalTarget n) ≤
        (1 / 1000000000 : ℚ)

theorem yoshidaFactorTwoCleanLowDiagonalTargetEnclosures :
    YoshidaFactorTwoCleanLowDiagonalTargetEnclosures := by
  intro n hn59
  exact ⟨yoshidaFactorTwoCleanLowDiagonalTarget_contains hn59,
    yoshidaFactorTwoCleanLowDiagonalTarget_width_le hn59⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCleanLowDiagonalEnclosures
