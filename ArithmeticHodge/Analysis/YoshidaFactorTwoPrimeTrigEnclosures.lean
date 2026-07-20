import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationMomentSeries
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

open Set
open scoped Nat

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeTrigEnclosures

noncomputable section

open RatInterval
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseConcretePerturbationMoments
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

/-!
# Exact enclosures for the retained `p = 3` phase

For the canonical modes `n = 0, ..., 200`, this file encloses

`sin (2 * factorTwoMomentY n * factorTwoPrimeShift)` and
`cos (2 * factorTwoMomentY n * factorTwoPrimeShift)`

in exact rational intervals of width at most `10^-10`.  The large phase is
reduced by a kernel-checked quarter-turn index, and sine and cosine on the
resulting interval `[-4/5, 4/5]` are enclosed by Taylor polynomials with a
rigorous remainder.
-/

/-! ## Fine logarithmic constants -/

/-- A `10^-14` rational enclosure of `log 2`. -/
def factorTwoPrimeLogTwoInterval : RatInterval :=
  ⟨69314718055994 / 100000000000000,
    69314718055995 / 100000000000000⟩

/-- A `10^-14` rational enclosure of the retained-prime shift `log (3/2)`. -/
def factorTwoPrimeShiftInterval : RatInterval :=
  ⟨40546510810816 / 100000000000000,
    40546510810817 / 100000000000000⟩

/-- The existing twenty-decimal rational enclosure of `pi`. -/
def factorTwoPrimePiInterval : RatInterval := piFineInterval

private theorem strict_log_two_prime_bounds :
    (69314718055994 / 100000000000000 : ℝ) < Real.log 2 ∧
      Real.log 2 < (69314718055995 / 100000000000000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 16
  have hup := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at hlo hup ⊢
  constructor <;> linarith

private theorem strict_log_three_halves_prime_bounds :
    (40546510810816 / 100000000000000 : ℝ) < Real.log (3 / 2) ∧
      Real.log (3 / 2) < (40546510810817 / 100000000000000 : ℝ) := by
  have hlo := Real.sum_range_le_log_div
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 10
  have hup := Real.log_div_le_sum_range_add
    (x := (1 / 5 : ℝ)) (by norm_num) (by norm_num) 10
  norm_num [Finset.sum_range_succ] at hlo hup ⊢
  constructor <;> linarith

theorem factorTwoPrimeLogTwoInterval_contains :
    factorTwoPrimeLogTwoInterval.Contains factorTwoMomentLength := by
  rw [factorTwoMomentLength_eq_yoshidaLength]
  constructor
  · have h := strict_log_two_prime_bounds.1
    norm_num [factorTwoPrimeLogTwoInterval, Contains, yoshidaLength] at h ⊢
    exact h.le
  · have h := strict_log_two_prime_bounds.2
    norm_num [factorTwoPrimeLogTwoInterval, Contains, yoshidaLength] at h ⊢
    exact h.le

theorem factorTwoPrimeShiftInterval_contains :
    factorTwoPrimeShiftInterval.Contains factorTwoPrimeShift := by
  constructor
  · have h := strict_log_three_halves_prime_bounds.1
    norm_num [factorTwoPrimeShiftInterval, Contains, factorTwoPrimeShift] at h ⊢
    exact h.le
  · have h := strict_log_three_halves_prime_bounds.2
    norm_num [factorTwoPrimeShiftInterval, Contains, factorTwoPrimeShift] at h ⊢
    exact h.le

theorem factorTwoPrimePiInterval_contains :
    factorTwoPrimePiInterval.Contains Real.pi := by
  exact piFineInterval_contains

/-! ## Quarter-turn reduction -/

/-- Nearest-quarter-turn certificate computed from the rational surrogate
`2.33985` for `4 * log (3/2) / log 2`. -/
def factorTwoPrimeQuarterIndex (n : Fin 201) : ℕ :=
  (233985 * n.1 + 50000) / 100000

/-- Direct rational enclosure of the unreduced retained-prime phase. -/
def factorTwoPrimePhaseInterval (n : Fin 201) : RatInterval :=
  pure 2 * factorTwoPrimePiInterval * pure n.1 *
      factorTwoPrimeShiftInterval / factorTwoPrimeLogTwoInterval

/-- Rational enclosure of `4 * log(3/2) / log 2`. -/
def factorTwoPrimeRatioInterval : RatInterval :=
  ⟨4 * factorTwoPrimeShiftInterval.lower /
      factorTwoPrimeLogTwoInterval.upper,
    4 * factorTwoPrimeShiftInterval.upper /
      factorTwoPrimeLogTwoInterval.lower⟩

/-- Cancellation-aware enclosure of the residual measured in quarter turns. -/
def factorTwoPrimeCenteredRatioInterval (n : Fin 201) : RatInterval :=
  ⟨factorTwoPrimeRatioInterval.lower * n.1 - factorTwoPrimeQuarterIndex n,
    factorTwoPrimeRatioInterval.upper * n.1 - factorTwoPrimeQuarterIndex n⟩

/-- Rational enclosure of `pi / 2`. -/
def factorTwoPrimePiHalfInterval : RatInterval :=
  ⟨factorTwoPrimePiInterval.lower / 2,
    factorTwoPrimePiInterval.upper / 2⟩

/-- Rational enclosure after subtracting the certified number of quarter
turns.  Factoring out `pi/2` retains the analytic cancellation and makes its
uniform width transparent. -/
def factorTwoPrimeResidualInterval (n : Fin 201) : RatInterval :=
  factorTwoPrimePiHalfInterval * factorTwoPrimeCenteredRatioInterval n

/-- The exact real reduced phase corresponding to
`factorTwoPrimeResidualInterval`. -/
def factorTwoPrimeResidual (n : Fin 201) : ℝ :=
  2 * factorTwoMomentY n.1 * factorTwoPrimeShift -
    factorTwoPrimeQuarterIndex n * Real.pi / 2

theorem factorTwoPrimePhaseInterval_contains (n : Fin 201) :
    (factorTwoPrimePhaseInterval n).Contains
      (2 * factorTwoMomentY n.1 * factorTwoPrimeShift) := by
  have hnum :
      (pure 2 * factorTwoPrimePiInterval * pure n.1 *
          factorTwoPrimeShiftInterval).Contains
        (2 * Real.pi * (n.1 : ℝ) * factorTwoPrimeShift) :=
    contains_mul
      (contains_mul
        (contains_mul (contains_pure 2) factorTwoPrimePiInterval_contains)
        (contains_pure n.1))
      factorTwoPrimeShiftInterval_contains
  have hphase := contains_div_of_pos
    (I := pure 2 * factorTwoPrimePiInterval * pure n.1 *
      factorTwoPrimeShiftInterval)
    (J := factorTwoPrimeLogTwoInterval)
    (by norm_num [factorTwoPrimeLogTwoInterval]) hnum
    factorTwoPrimeLogTwoInterval_contains
  unfold factorTwoPrimePhaseInterval
  convert hphase using 1
  unfold factorTwoMomentY factorTwoNaturalFrequency
  rw [factorTwoMomentLength_eq_yoshidaLength]
  ring

theorem factorTwoPrimeRatioInterval_contains :
    factorTwoPrimeRatioInterval.Contains
      (4 * factorTwoPrimeShift / factorTwoMomentLength) := by
  have hshiftPos : 0 < factorTwoPrimeShift :=
    (show (0 : ℝ) < factorTwoPrimeShiftInterval.lower by
      norm_num [factorTwoPrimeShiftInterval]).trans_le
        factorTwoPrimeShiftInterval_contains.1
  have hnum0 : 0 ≤ 4 * factorTwoPrimeShift :=
    mul_nonneg (by norm_num) hshiftPos.le
  have hnumLo :
      (4 : ℝ) * (factorTwoPrimeShiftInterval.lower : ℝ) ≤
        (4 * factorTwoPrimeShift : ℝ) := by
    exact mul_le_mul_of_nonneg_left factorTwoPrimeShiftInterval_contains.1
      (by norm_num)
  have hnumHi :
      (4 * factorTwoPrimeShift : ℝ) ≤
        (4 : ℝ) * (factorTwoPrimeShiftInterval.upper : ℝ) := by
    exact mul_le_mul_of_nonneg_left factorTwoPrimeShiftInterval_contains.2
      (by norm_num)
  have hlogLowerPos :
      (0 : ℝ) < factorTwoPrimeLogTwoInterval.lower := by
    norm_num [factorTwoPrimeLogTwoInterval]
  unfold factorTwoPrimeRatioInterval
  constructor
  · norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    exact div_le_div₀ hnum0 hnumLo factorTwoMomentLength_pos
      factorTwoPrimeLogTwoInterval_contains.2
  · norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    exact div_le_div₀
      (by norm_num [factorTwoPrimeShiftInterval]) hnumHi hlogLowerPos
      factorTwoPrimeLogTwoInterval_contains.1

theorem factorTwoPrimeCenteredRatioInterval_contains (n : Fin 201) :
    (factorTwoPrimeCenteredRatioInterval n).Contains
      (4 * factorTwoPrimeShift / factorTwoMomentLength * n.1 -
        factorTwoPrimeQuarterIndex n) := by
  have hratio := factorTwoPrimeRatioInterval_contains
  constructor
  · norm_num only [factorTwoPrimeCenteredRatioInterval, Contains,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast]
    exact sub_le_sub_right
      (mul_le_mul_of_nonneg_right hratio.1 (by positivity)) _
  · norm_num only [factorTwoPrimeCenteredRatioInterval, Contains,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast]
    exact sub_le_sub_right
      (mul_le_mul_of_nonneg_right hratio.2 (by positivity)) _

theorem factorTwoPrimePiHalfInterval_contains :
    factorTwoPrimePiHalfInterval.Contains (Real.pi / 2) := by
  constructor
  · norm_num only [factorTwoPrimePiHalfInterval, Contains, Rat.cast_div,
      Rat.cast_ofNat]
    exact div_le_div_of_nonneg_right factorTwoPrimePiInterval_contains.1
      (by norm_num)
  · norm_num only [factorTwoPrimePiHalfInterval, Contains, Rat.cast_div,
      Rat.cast_ofNat]
    exact div_le_div_of_nonneg_right factorTwoPrimePiInterval_contains.2
      (by norm_num)

theorem factorTwoPrimeResidualInterval_contains (n : Fin 201) :
    (factorTwoPrimeResidualInterval n).Contains
      (factorTwoPrimeResidual n) := by
  have h := contains_mul factorTwoPrimePiHalfInterval_contains
    (factorTwoPrimeCenteredRatioInterval_contains n)
  unfold factorTwoPrimeResidual factorTwoPrimeResidualInterval
    factorTwoMomentY factorTwoNaturalFrequency
  convert h using 1
  ring

private theorem factorTwoPrimeRatioInterval_valid :
    factorTwoPrimeRatioInterval.Valid := by
  change
    4 * factorTwoPrimeShiftInterval.lower /
        factorTwoPrimeLogTwoInterval.upper ≤
      4 * factorTwoPrimeShiftInterval.upper /
        factorTwoPrimeLogTwoInterval.lower
  norm_num [factorTwoPrimeShiftInterval, factorTwoPrimeLogTwoInterval]

private theorem factorTwoPrimeRatioInterval_lower_ge_surrogate :
    (233985 / 100000 : ℚ) ≤ factorTwoPrimeRatioInterval.lower := by
  change (233985 / 100000 : ℚ) ≤
    4 * factorTwoPrimeShiftInterval.lower /
      factorTwoPrimeLogTwoInterval.upper
  norm_num [factorTwoPrimeShiftInterval, factorTwoPrimeLogTwoInterval]

private theorem factorTwoPrimeRatioInterval_upper_le_surrogate :
    factorTwoPrimeRatioInterval.upper ≤
      (233985 / 100000 : ℚ) + 3 / 1000000000 := by
  change
    4 * factorTwoPrimeShiftInterval.upper /
        factorTwoPrimeLogTwoInterval.lower ≤
      (233985 / 100000 : ℚ) + 3 / 1000000000
  norm_num [factorTwoPrimeShiftInterval, factorTwoPrimeLogTwoInterval]

private theorem factorTwoPrimeQuarterIndex_le_surrogate (n : Fin 201) :
    (factorTwoPrimeQuarterIndex n : ℚ) ≤
      (233985 / 100000 : ℚ) * n.1 + 1 / 2 := by
  have hnat := Nat.div_mul_le_self (233985 * n.1 + 50000) 100000
  have hq : factorTwoPrimeQuarterIndex n * 100000 ≤
      233985 * n.1 + 50000 := by
    simpa only [factorTwoPrimeQuarterIndex] using hnat
  have hqQ :
      (factorTwoPrimeQuarterIndex n : ℚ) * 100000 ≤
        233985 * n.1 + 50000 := by
    exact_mod_cast hq
  norm_num at hqQ ⊢
  linarith

private theorem surrogate_sub_half_lt_factorTwoPrimeQuarterIndex
    (n : Fin 201) :
    (233985 / 100000 : ℚ) * n.1 - 1 / 2 <
      factorTwoPrimeQuarterIndex n := by
  have hnat := Nat.lt_mul_div_succ (233985 * n.1 + 50000)
    (by norm_num : 0 < 100000)
  have hq : 233985 * n.1 + 50000 <
      100000 * (factorTwoPrimeQuarterIndex n + 1) := by
    simpa only [factorTwoPrimeQuarterIndex] using hnat
  have hqQ :
      (233985 * n.1 + 50000 : ℚ) <
        100000 * (factorTwoPrimeQuarterIndex n + 1) := by
    exact_mod_cast hq
  norm_num at hqQ ⊢
  linarith

private theorem factorTwoPrimeCenteredRatioInterval_valid (n : Fin 201) :
    (factorTwoPrimeCenteredRatioInterval n).Valid := by
  change factorTwoPrimeRatioInterval.lower * n.1 -
      factorTwoPrimeQuarterIndex n ≤
    factorTwoPrimeRatioInterval.upper * n.1 -
      factorTwoPrimeQuarterIndex n
  exact sub_le_sub_right
    (mul_le_mul_of_nonneg_right factorTwoPrimeRatioInterval_valid
      (by positivity)) _

private theorem factorTwoPrimeCenteredRatioInterval_absBound (n : Fin 201) :
    (factorTwoPrimeCenteredRatioInterval n).AbsBound (501 / 1000) := by
  have hn200 : n.1 ≤ 200 := by omega
  have hlo := factorTwoPrimeRatioInterval_lower_ge_surrogate
  have hup := factorTwoPrimeRatioInterval_upper_le_surrogate
  have hqlo := surrogate_sub_half_lt_factorTwoPrimeQuarterIndex n
  have hqhi := factorTwoPrimeQuarterIndex_le_surrogate n
  unfold AbsBound factorTwoPrimeCenteredRatioInterval
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hlo
      (show (0 : ℚ) ≤ n.1 by positivity)
    linarith
  · have hmul := mul_le_mul_of_nonneg_right hup
      (show (0 : ℚ) ≤ n.1 by positivity)
    have hnQ : (n.1 : ℚ) ≤ 200 := by exact_mod_cast hn200
    nlinarith

private theorem factorTwoPrimePiHalfInterval_valid :
    factorTwoPrimePiHalfInterval.Valid := by
  change factorTwoPrimePiInterval.lower / 2 ≤
    factorTwoPrimePiInterval.upper / 2
  exact div_le_div_of_nonneg_right
    (valid_of_contains factorTwoPrimePiInterval_contains) (by norm_num)

private theorem factorTwoPrimePiHalfInterval_absBound :
    factorTwoPrimePiHalfInterval.AbsBound (1571 / 1000) := by
  unfold AbsBound factorTwoPrimePiHalfInterval factorTwoPrimePiInterval
  constructor <;> norm_num [piFineInterval]

private theorem factorTwoPrimeResidualInterval_valid (n : Fin 201) :
    (factorTwoPrimeResidualInterval n).Valid := by
  exact valid_mul factorTwoPrimePiHalfInterval_valid
    (factorTwoPrimeCenteredRatioInterval_valid n)

theorem factorTwoPrimeResidualInterval_absBound
    (n : Fin 201) :
    (factorTwoPrimeResidualInterval n).AbsBound (4 / 5) := by
  have hsmall := absBound_mul factorTwoPrimePiHalfInterval_valid
    (factorTwoPrimeCenteredRatioInterval_valid n)
    factorTwoPrimePiHalfInterval_absBound
    (factorTwoPrimeCenteredRatioInterval_absBound n)
    (by norm_num : (0 : ℚ) ≤ 1571 / 1000)
    (by norm_num : (0 : ℚ) ≤ 501 / 1000)
  have hB : (1571 / 1000 : ℚ) * (501 / 1000) ≤ 4 / 5 := by
    norm_num
  unfold AbsBound at hsmall ⊢
  exact ⟨(neg_le_neg hB).trans hsmall.1, hsmall.2.trans hB⟩

theorem factorTwoPrimeResidual_abs_le (n : Fin 201) :
    |factorTwoPrimeResidual n| ≤ (4 / 5 : ℝ) := by
  have hmem := factorTwoPrimeResidualInterval_contains n
  have hbox := factorTwoPrimeResidualInterval_absBound n
  rw [abs_le]
  constructor
  · calc
      -(4 / 5 : ℝ) ≤ ((factorTwoPrimeResidualInterval n).lower : ℝ) := by
        simpa using (Rat.cast_le (K := ℝ)).2 hbox.1
      _ ≤ factorTwoPrimeResidual n := hmem.1
  · calc
      factorTwoPrimeResidual n ≤
          ((factorTwoPrimeResidualInterval n).upper : ℝ) := hmem.2
      _ ≤ (4 / 5 : ℝ) := by
        simpa using (Rat.cast_le (K := ℝ)).2 hbox.2

/-! ## Structural residual metrics -/

private theorem factorTwoPrimeRatioInterval_width_le :
    width factorTwoPrimeRatioInterval ≤ (1 / 10000000000000 : ℚ) := by
  norm_num [width, factorTwoPrimeRatioInterval,
    factorTwoPrimeShiftInterval, factorTwoPrimeLogTwoInterval]

private theorem factorTwoPrimeCenteredRatioInterval_width_le
    (n : Fin 201) :
    width (factorTwoPrimeCenteredRatioInterval n) ≤
      (1 / 50000000000 : ℚ) := by
  have hn200 : (n.1 : ℚ) ≤ 200 := by
    exact_mod_cast (show n.1 ≤ 200 by omega)
  change
    (factorTwoPrimeRatioInterval.upper * n.1 -
        factorTwoPrimeQuarterIndex n) -
      (factorTwoPrimeRatioInterval.lower * n.1 -
        factorTwoPrimeQuarterIndex n) ≤ (1 / 50000000000 : ℚ)
  calc
    (factorTwoPrimeRatioInterval.upper * n.1 -
          factorTwoPrimeQuarterIndex n) -
        (factorTwoPrimeRatioInterval.lower * n.1 -
          factorTwoPrimeQuarterIndex n) =
      width factorTwoPrimeRatioInterval * n.1 := by
        unfold width
        ring
    _ ≤ (1 / 10000000000000 : ℚ) * n.1 := by
      exact mul_le_mul_of_nonneg_right
        factorTwoPrimeRatioInterval_width_le (by positivity)
    _ ≤ (1 / 10000000000000 : ℚ) * 200 := by
      exact mul_le_mul_of_nonneg_left hn200 (by norm_num)
    _ = (1 / 50000000000 : ℚ) := by norm_num

private theorem factorTwoPrimePiHalfInterval_width_le :
    width factorTwoPrimePiHalfInterval ≤
      (1 / 200000000000000000000 : ℚ) := by
  norm_num [width, factorTwoPrimePiHalfInterval,
    factorTwoPrimePiInterval, piFineInterval]

private theorem factorTwoPrimeResidualInterval_width_le_structural
    (n : Fin 201) :
    width (factorTwoPrimeResidualInterval n) ≤
      (1 / 30000000000 : ℚ) := by
  have hmul := width_mul_le factorTwoPrimePiHalfInterval_valid
    (factorTwoPrimeCenteredRatioInterval_valid n)
    factorTwoPrimePiHalfInterval_absBound
    (factorTwoPrimeCenteredRatioInterval_absBound n)
    (by norm_num : (0 : ℚ) ≤ 1571 / 1000)
    (by norm_num : (0 : ℚ) ≤ 501 / 1000)
  calc
    width (factorTwoPrimeResidualInterval n) ≤
        (501 / 1000 : ℚ) * width factorTwoPrimePiHalfInterval +
          (1571 / 1000 : ℚ) *
            width (factorTwoPrimeCenteredRatioInterval n) := by
      simpa only [factorTwoPrimeResidualInterval] using hmul
    _ ≤ (501 / 1000 : ℚ) *
          (1 / 200000000000000000000 : ℚ) +
        (1571 / 1000 : ℚ) * (1 / 50000000000 : ℚ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left factorTwoPrimePiHalfInterval_width_le
          (by norm_num))
        (mul_le_mul_of_nonneg_left
          (factorTwoPrimeCenteredRatioInterval_width_le n) (by norm_num))
    _ ≤ (1 / 30000000000 : ℚ) := by norm_num

/-! ## Taylor enclosure on `[-4/5, 4/5]` -/

private def factorTwoPrimeSinTaylor (x : ℝ) : ℝ :=
  let z := x * x
  x * (1 + z * (-1 / 6 + z * (1 / 120 + z *
    (-1 / 5040 + z * (1 / 362880 + z *
      (-1 / 39916800 + z * (1 / 6227020800)))))))

private def factorTwoPrimeCosTaylor (x : ℝ) : ℝ :=
  let z := x * x
  1 + z * (-1 / 2 + z * (1 / 24 + z *
    (-1 / 720 + z * (1 / 40320 + z *
      (-1 / 3628800 + z * (1 / 479001600))))))

/-- Rational Taylor remainder used for both sine and cosine. -/
def factorTwoPrimeTaylorError : ℚ :=
  (4 / 5) ^ 14 / 6227020800

def factorTwoPrimeTaylorErrorInterval : RatInterval :=
  ⟨-factorTwoPrimeTaylorError, factorTwoPrimeTaylorError⟩

/-- Horner evaluation of the degree-13 sine Taylor polynomial. -/
def factorTwoPrimeSinTaylorInterval (I : RatInterval) : RatInterval :=
  let z := I * I
  I * (pure 1 + z * (pure (-1 / 6) + z * (pure (1 / 120) + z *
    (pure (-1 / 5040) + z * (pure (1 / 362880) + z *
      (pure (-1 / 39916800) + z * pure (1 / 6227020800)))))))

/-- Horner evaluation of the degree-12 cosine Taylor polynomial. -/
def factorTwoPrimeCosTaylorInterval (I : RatInterval) : RatInterval :=
  let z := I * I
  pure 1 + z * (pure (-1 / 2) + z * (pure (1 / 24) + z *
    (pure (-1 / 720) + z * (pure (1 / 40320) + z *
      (pure (-1 / 3628800) + z * pure (1 / 479001600))))))

private theorem absBound_mono
    {I : RatInterval} {B C : ℚ} (hI : I.AbsBound B) (hBC : B ≤ C) :
    I.AbsBound C := by
  unfold AbsBound at hI ⊢
  exact ⟨(neg_le_neg hBC).trans hI.1, hI.2.trans hBC⟩

/-- One structural Horner step, tracking validity, magnitude, and width. -/
private theorem hornerStep_metrics
    (c : ℚ) {Z H : RatInterval}
    {BZ BH WZ WH B W : ℚ}
    (hZvalid : Z.Valid) (hHvalid : H.Valid)
    (hZabs : Z.AbsBound BZ) (hHabs : H.AbsBound BH)
    (hBZ : 0 ≤ BZ) (hBH : 0 ≤ BH)
    (hZwidth : width Z ≤ WZ) (hHwidth : width H ≤ WH)
    (_hWZ : 0 ≤ WZ) (_hWH : 0 ≤ WH)
    (hB : |c| + BZ * BH ≤ B)
    (hW : BH * WZ + BZ * WH ≤ W) :
    let R := pure c + Z * H
    R.Valid ∧ R.AbsBound B ∧ width R ≤ W := by
  dsimp only
  have hProdValid := valid_mul hZvalid hHvalid
  have hProdAbs := absBound_mul hZvalid hHvalid hZabs hHabs hBZ hBH
  have hProdWidth := width_mul_le hZvalid hHvalid hZabs hHabs hBZ hBH
  constructor
  · exact valid_add (valid_pure c) hProdValid
  constructor
  · exact absBound_mono (absBound_add (absBound_pure le_rfl) hProdAbs) hB
  · rw [width_add, width_pure, zero_add]
    calc
      width (Z * H) ≤ BH * width Z + BZ * width H := hProdWidth
      _ ≤ BH * WZ + BZ * WH := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hZwidth hBH)
          (mul_le_mul_of_nonneg_left hHwidth hBZ)
      _ ≤ W := hW

private theorem squareInterval_metrics
    {I : RatInterval} {w : ℚ}
    (hIvalid : I.Valid) (hIabs : I.AbsBound (4 / 5))
    (hIwidth : width I ≤ w) (_hw : 0 ≤ w) :
    let Z := I * I
    Z.Valid ∧ Z.AbsBound (16 / 25) ∧ width Z ≤ (8 / 5) * w := by
  dsimp only
  constructor
  · exact valid_mul hIvalid hIvalid
  constructor
  · have h := absBound_mul hIvalid hIvalid hIabs hIabs
      (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  · calc
      width (I * I) ≤ (4 / 5 : ℚ) * width I +
          (4 / 5 : ℚ) * width I :=
        width_mul_le hIvalid hIvalid hIabs hIabs (by norm_num) (by norm_num)
      _ ≤ (4 / 5 : ℚ) * w + (4 / 5 : ℚ) * w :=
        add_le_add
          (mul_le_mul_of_nonneg_left hIwidth (by norm_num))
          (mul_le_mul_of_nonneg_left hIwidth (by norm_num))
      _ = (8 / 5 : ℚ) * w := by ring

private theorem factorTwoPrimeSinTaylorInterval_width_le_structural
    {I : RatInterval} {w : ℚ}
    (hIvalid : I.Valid) (hIabs : I.AbsBound (4 / 5))
    (hIwidth : width I ≤ w) (hw : 0 ≤ w) :
    width (factorTwoPrimeSinTaylorInterval I) ≤ (3 / 2) * w := by
  let Z := I * I
  have hZ := squareInterval_metrics hIvalid hIabs hIwidth hw
  change Z.Valid ∧ Z.AbsBound (16 / 25) ∧
    width Z ≤ (8 / 5) * w at hZ
  let H6 : RatInterval := pure (1 / 6227020800)
  have hH6valid : H6.Valid := by
    exact valid_pure _
  have hH6abs : H6.AbsBound (1 / 1000000000) := by
    apply absBound_pure
    norm_num [H6]
  have hH6width : width H6 ≤ 0 := by
    simp only [H6, width_pure, le_refl]
  let H5 := pure (-1 / 39916800) + Z * H6
  have hH5 := hornerStep_metrics (-1 / 39916800)
    hZ.1 hH6valid hZ.2.1 hH6abs
    (by norm_num) (by norm_num) hZ.2.2 hH6width
    (mul_nonneg (by norm_num) hw) (by norm_num)
    (B := 1 / 30000000) (W := (1 / 500000000) * w)
    (by norm_num) (by nlinarith)
  change H5.Valid ∧ H5.AbsBound (1 / 30000000) ∧
    width H5 ≤ (1 / 500000000) * w at hH5
  let H4 := pure (1 / 362880) + Z * H5
  have hH4 := hornerStep_metrics (1 / 362880)
    hZ.1 hH5.1 hZ.2.1 hH5.2.1
    (by norm_num) (by norm_num) hZ.2.2 hH5.2.2
    (mul_nonneg (by norm_num) hw) (mul_nonneg (by norm_num) hw)
    (B := 1 / 300000) (W := (1 / 18000000) * w)
    (by norm_num) (by nlinarith)
  change H4.Valid ∧ H4.AbsBound (1 / 300000) ∧
    width H4 ≤ (1 / 18000000) * w at hH4
  let H3 := pure (-1 / 5040) + Z * H4
  have hH3 := hornerStep_metrics (-1 / 5040)
    hZ.1 hH4.1 hZ.2.1 hH4.2.1
    (by norm_num) (by norm_num) hZ.2.2 hH4.2.2
    (mul_nonneg (by norm_num) hw) (mul_nonneg (by norm_num) hw)
    (B := 1 / 4000) (W := (1 / 180000) * w)
    (by norm_num) (by nlinarith)
  change H3.Valid ∧ H3.AbsBound (1 / 4000) ∧
    width H3 ≤ (1 / 180000) * w at hH3
  let H2 := pure (1 / 120) + Z * H3
  have hH2 := hornerStep_metrics (1 / 120)
    hZ.1 hH3.1 hZ.2.1 hH3.2.1
    (by norm_num) (by norm_num) hZ.2.2 hH3.2.2
    (mul_nonneg (by norm_num) hw) (mul_nonneg (by norm_num) hw)
    (B := 1 / 100) (W := (1 / 2400) * w)
    (by norm_num) (by nlinarith)
  change H2.Valid ∧ H2.AbsBound (1 / 100) ∧
    width H2 ≤ (1 / 2400) * w at hH2
  let H1 := pure (-1 / 6) + Z * H2
  have hH1 := hornerStep_metrics (-1 / 6)
    hZ.1 hH2.1 hZ.2.1 hH2.2.1
    (by norm_num) (by norm_num) hZ.2.2 hH2.2.2
    (mul_nonneg (by norm_num) hw) (mul_nonneg (by norm_num) hw)
    (B := 1 / 5) (W := (1 / 60) * w)
    (by norm_num) (by nlinarith)
  change H1.Valid ∧ H1.AbsBound (1 / 5) ∧
    width H1 ≤ (1 / 60) * w at hH1
  let H0 := pure 1 + Z * H1
  have hH0 := hornerStep_metrics 1
    hZ.1 hH1.1 hZ.2.1 hH1.2.1
    (by norm_num) (by norm_num) hZ.2.2 hH1.2.2
    (mul_nonneg (by norm_num) hw) (mul_nonneg (by norm_num) hw)
    (B := 6 / 5) (W := (1 / 3) * w)
    (by norm_num) (by nlinarith)
  change H0.Valid ∧ H0.AbsBound (6 / 5) ∧
    width H0 ≤ (1 / 3) * w at hH0
  have hfinal := width_mul_le hIvalid hH0.1 hIabs hH0.2.1
    (by norm_num : (0 : ℚ) ≤ 4 / 5) (by norm_num : (0 : ℚ) ≤ 6 / 5)
  change width (I * H0) ≤ (3 / 2) * w
  calc
    width (I * H0) ≤ (6 / 5 : ℚ) * width I +
        (4 / 5 : ℚ) * width H0 := hfinal
    _ ≤ (6 / 5 : ℚ) * w + (4 / 5 : ℚ) * ((1 / 3) * w) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hIwidth (by norm_num))
        (mul_le_mul_of_nonneg_left hH0.2.2 (by norm_num))
    _ ≤ (3 / 2 : ℚ) * w := by nlinarith

private theorem factorTwoPrimeCosTaylorInterval_width_le_structural
    {I : RatInterval} {w : ℚ}
    (hIvalid : I.Valid) (hIabs : I.AbsBound (4 / 5))
    (hIwidth : width I ≤ w) (hw : 0 ≤ w) :
    width (factorTwoPrimeCosTaylorInterval I) ≤ (9 / 10) * w := by
  let Z := I * I
  have hZ := squareInterval_metrics hIvalid hIabs hIwidth hw
  change Z.Valid ∧ Z.AbsBound (16 / 25) ∧
    width Z ≤ (8 / 5) * w at hZ
  let H6 : RatInterval := pure (1 / 479001600)
  have hH6valid : H6.Valid := by
    exact valid_pure _
  have hH6abs : H6.AbsBound (1 / 400000000) := by
    apply absBound_pure
    norm_num [H6]
  have hH6width : width H6 ≤ 0 := by
    simp only [H6, width_pure, le_refl]
  let H5 := pure (-1 / 3628800) + Z * H6
  have hH5 := hornerStep_metrics (-1 / 3628800)
    hZ.1 hH6valid hZ.2.1 hH6abs
    (by norm_num) (by norm_num) hZ.2.2 hH6width
    (mul_nonneg (by norm_num) hw) (by norm_num)
    (B := 1 / 3000000) (W := (1 / 250000000) * w)
    (by norm_num) (by nlinarith)
  change H5.Valid ∧ H5.AbsBound (1 / 3000000) ∧
    width H5 ≤ (1 / 250000000) * w at hH5
  let H4 := pure (1 / 40320) + Z * H5
  have hH4 := hornerStep_metrics (1 / 40320)
    hZ.1 hH5.1 hZ.2.1 hH5.2.1
    (by norm_num) (by norm_num) hZ.2.2 hH5.2.2
    (mul_nonneg (by norm_num) hw) (mul_nonneg (by norm_num) hw)
    (B := 1 / 38000) (W := (1 / 1800000) * w)
    (by norm_num) (by nlinarith)
  change H4.Valid ∧ H4.AbsBound (1 / 38000) ∧
    width H4 ≤ (1 / 1800000) * w at hH4
  let H3 := pure (-1 / 720) + Z * H4
  have hH3 := hornerStep_metrics (-1 / 720)
    hZ.1 hH4.1 hZ.2.1 hH4.2.1
    (by norm_num) (by norm_num) hZ.2.2 hH4.2.2
    (mul_nonneg (by norm_num) hw) (mul_nonneg (by norm_num) hw)
    (B := 1 / 700) (W := (1 / 23000) * w)
    (by norm_num) (by nlinarith)
  change H3.Valid ∧ H3.AbsBound (1 / 700) ∧
    width H3 ≤ (1 / 23000) * w at hH3
  let H2 := pure (1 / 24) + Z * H3
  have hH2 := hornerStep_metrics (1 / 24)
    hZ.1 hH3.1 hZ.2.1 hH3.2.1
    (by norm_num) (by norm_num) hZ.2.2 hH3.2.2
    (mul_nonneg (by norm_num) hw) (mul_nonneg (by norm_num) hw)
    (B := 1 / 23) (W := (1 / 430) * w)
    (by norm_num) (by nlinarith)
  change H2.Valid ∧ H2.AbsBound (1 / 23) ∧
    width H2 ≤ (1 / 430) * w at hH2
  let H1 := pure (-1 / 2) + Z * H2
  have hH1 := hornerStep_metrics (-1 / 2)
    hZ.1 hH2.1 hZ.2.1 hH2.2.1
    (by norm_num) (by norm_num) hZ.2.2 hH2.2.2
    (mul_nonneg (by norm_num) hw) (mul_nonneg (by norm_num) hw)
    (B := 8 / 15) (W := (1 / 14) * w)
    (by norm_num) (by nlinarith)
  change H1.Valid ∧ H1.AbsBound (8 / 15) ∧
    width H1 ≤ (1 / 14) * w at hH1
  let H0 := pure 1 + Z * H1
  have hH0 := hornerStep_metrics 1
    hZ.1 hH1.1 hZ.2.1 hH1.2.1
    (by norm_num) (by norm_num) hZ.2.2 hH1.2.2
    (mul_nonneg (by norm_num) hw) (mul_nonneg (by norm_num) hw)
    (B := 7 / 5) (W := (9 / 10) * w)
    (by norm_num) (by nlinarith)
  change H0.Valid ∧ H0.AbsBound (7 / 5) ∧
    width H0 ≤ (9 / 10) * w at hH0
  change width H0 ≤ (9 / 10) * w
  exact hH0.2.2

private theorem factorTwoPrimeTaylorErrorInterval_width_le :
    width factorTwoPrimeTaylorErrorInterval ≤
      (1 / 70000000000 : ℚ) := by
  norm_num [width, factorTwoPrimeTaylorErrorInterval,
    factorTwoPrimeTaylorError]

private theorem factorTwoPrimeSinTaylor_error_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ (4 / 5 : ℝ)) :
    |Real.sin x - factorTwoPrimeSinTaylor x| ≤
      (4 / 5 : ℝ) ^ 14 / 13 ! := by
  have hpos : (0 : ℝ) < 4 / 5 := by norm_num
  have hzero : (0 : ℝ) ∈ Icc 0 (4 / 5) := by norm_num
  have ht :
      taylorWithinEval Real.sin 13 (Icc 0 (4 / 5)) 0 x =
        factorTwoPrimeSinTaylor x := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ,
      Real.iteratedDerivWithin_sin_Icc _ hpos hzero,
      factorTwoPrimeSinTaylor]
    ring
  have h := taylor_mean_remainder_bound
    (f := Real.sin) (a := 0) (b := (4 / 5 : ℝ))
    (C := 1) (x := x) (n := 13)
    (by norm_num) Real.contDiff_sin.contDiffOn ⟨hx0, hx1⟩ (by
      intro y hy
      rw [Real.iteratedDerivWithin_sin_Icc 14 hpos hy, Real.norm_eq_abs]
      exact Real.abs_iteratedDeriv_sin_le_one 14 y)
  rw [ht] at h
  norm_num only [one_mul, sub_zero] at h
  have hp : x ^ 14 ≤ (4 / 5 : ℝ) ^ 14 :=
    pow_le_pow_left₀ hx0 hx1 14
  norm_num [Nat.factorial] at h ⊢
  exact h.trans (by linarith)

private theorem factorTwoPrimeCosTaylor_error_nonneg
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ (4 / 5 : ℝ)) :
    |Real.cos x - factorTwoPrimeCosTaylor x| ≤
      (4 / 5 : ℝ) ^ 14 / 13 ! := by
  have hpos : (0 : ℝ) < 4 / 5 := by norm_num
  have hzero : (0 : ℝ) ∈ Icc 0 (4 / 5) := by norm_num
  have ht :
      taylorWithinEval Real.cos 13 (Icc 0 (4 / 5)) 0 x =
        factorTwoPrimeCosTaylor x := by
    rw [taylor_within_apply]
    simp [Finset.sum_range_succ,
      Real.iteratedDerivWithin_cos_Icc _ hpos hzero,
      factorTwoPrimeCosTaylor]
    ring
  have h := taylor_mean_remainder_bound
    (f := Real.cos) (a := 0) (b := (4 / 5 : ℝ))
    (C := 1) (x := x) (n := 13)
    (by norm_num) Real.contDiff_cos.contDiffOn ⟨hx0, hx1⟩ (by
      intro y hy
      rw [Real.iteratedDerivWithin_cos_Icc 14 hpos hy, Real.norm_eq_abs]
      exact Real.abs_iteratedDeriv_cos_le_one 14 y)
  rw [ht] at h
  norm_num only [one_mul, sub_zero] at h
  have hp : x ^ 14 ≤ (4 / 5 : ℝ) ^ 14 :=
    pow_le_pow_left₀ hx0 hx1 14
  norm_num [Nat.factorial] at h ⊢
  exact h.trans (by linarith)

private theorem factorTwoPrimeSinTaylor_error
    {x : ℝ} (hx : |x| ≤ (4 / 5 : ℝ)) :
    |Real.sin x - factorTwoPrimeSinTaylor x| ≤
      (4 / 5 : ℝ) ^ 14 / 13 ! := by
  by_cases h : 0 ≤ x
  · exact factorTwoPrimeSinTaylor_error_nonneg h
      (by simpa [abs_of_nonneg h] using hx)
  · have hn : x < 0 := lt_of_not_ge h
    have hu := factorTwoPrimeSinTaylor_error_nonneg
      (x := -x) (by linarith) (by simpa [abs_of_neg hn] using hx)
    have hi :
        Real.sin (-x) - factorTwoPrimeSinTaylor (-x) =
          -(Real.sin x - factorTwoPrimeSinTaylor x) := by
      rw [Real.sin_neg]
      simp only [factorTwoPrimeSinTaylor]
      ring
    rw [hi, abs_neg] at hu
    exact hu

private theorem factorTwoPrimeCosTaylor_error
    {x : ℝ} (hx : |x| ≤ (4 / 5 : ℝ)) :
    |Real.cos x - factorTwoPrimeCosTaylor x| ≤
      (4 / 5 : ℝ) ^ 14 / 13 ! := by
  by_cases h : 0 ≤ x
  · exact factorTwoPrimeCosTaylor_error_nonneg h
      (by simpa [abs_of_nonneg h] using hx)
  · have hn : x < 0 := lt_of_not_ge h
    have hu := factorTwoPrimeCosTaylor_error_nonneg
      (x := -x) (by linarith) (by simpa [abs_of_neg hn] using hx)
    have hi :
        Real.cos (-x) - factorTwoPrimeCosTaylor (-x) =
          Real.cos x - factorTwoPrimeCosTaylor x := by
      rw [Real.cos_neg]
      simp only [factorTwoPrimeCosTaylor]
      ring
    rw [hi] at hu
    exact hu

private theorem factorTwoPrimeSinTaylorInterval_contains
    {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (factorTwoPrimeSinTaylorInterval I).Contains
      (factorTwoPrimeSinTaylor x) := by
  have hz := contains_mul hx hx
  have h6 := contains_add (contains_pure (-1 / 39916800))
    (contains_mul hz (contains_pure (1 / 6227020800)))
  have h5 := contains_add (contains_pure (1 / 362880)) (contains_mul hz h6)
  have h4 := contains_add (contains_pure (-1 / 5040)) (contains_mul hz h5)
  have h3 := contains_add (contains_pure (1 / 120)) (contains_mul hz h4)
  have h2 := contains_add (contains_pure (-1 / 6)) (contains_mul hz h3)
  have h1 := contains_add (contains_pure 1) (contains_mul hz h2)
  simpa [factorTwoPrimeSinTaylorInterval, factorTwoPrimeSinTaylor] using
    contains_mul hx h1

private theorem factorTwoPrimeCosTaylorInterval_contains
    {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (factorTwoPrimeCosTaylorInterval I).Contains
      (factorTwoPrimeCosTaylor x) := by
  have hz := contains_mul hx hx
  have h6 := contains_add (contains_pure (-1 / 3628800))
    (contains_mul hz (contains_pure (1 / 479001600)))
  have h5 := contains_add (contains_pure (1 / 40320)) (contains_mul hz h6)
  have h4 := contains_add (contains_pure (-1 / 720)) (contains_mul hz h5)
  have h3 := contains_add (contains_pure (1 / 24)) (contains_mul hz h4)
  have h2 := contains_add (contains_pure (-1 / 2)) (contains_mul hz h3)
  have h1 := contains_add (contains_pure 1) (contains_mul hz h2)
  simpa [factorTwoPrimeCosTaylorInterval, factorTwoPrimeCosTaylor] using h1

private theorem factorTwoPrimeTaylorErrorInterval_contains
    {x : ℝ}
    (hx : |x| ≤ (4 / 5 : ℝ) ^ 14 / 13 !) :
    factorTwoPrimeTaylorErrorInterval.Contains x := by
  have hx' : |x| ≤ ((factorTwoPrimeTaylorError : ℚ) : ℝ) := by
    simpa [factorTwoPrimeTaylorError, Nat.factorial] using hx
  simpa [factorTwoPrimeTaylorErrorInterval, Contains] using (abs_le.mp hx')

/-- Sine enclosure before restoring the removed quarter turns. -/
def factorTwoPrimeReducedSinInterval (n : Fin 201) : RatInterval :=
  factorTwoPrimeSinTaylorInterval (factorTwoPrimeResidualInterval n) +
    factorTwoPrimeTaylorErrorInterval

/-- Cosine enclosure before restoring the removed quarter turns. -/
def factorTwoPrimeReducedCosInterval (n : Fin 201) : RatInterval :=
  factorTwoPrimeCosTaylorInterval (factorTwoPrimeResidualInterval n) +
    factorTwoPrimeTaylorErrorInterval

theorem factorTwoPrimeReducedSinInterval_contains (n : Fin 201) :
    (factorTwoPrimeReducedSinInterval n).Contains
      (Real.sin (factorTwoPrimeResidual n)) := by
  have hp := factorTwoPrimeSinTaylorInterval_contains
    (factorTwoPrimeResidualInterval_contains n)
  have he := factorTwoPrimeTaylorErrorInterval_contains
    (factorTwoPrimeSinTaylor_error (factorTwoPrimeResidual_abs_le n))
  have h := contains_add hp he
  unfold factorTwoPrimeReducedSinInterval
  convert h using 1
  ring

theorem factorTwoPrimeReducedCosInterval_contains (n : Fin 201) :
    (factorTwoPrimeReducedCosInterval n).Contains
      (Real.cos (factorTwoPrimeResidual n)) := by
  have hp := factorTwoPrimeCosTaylorInterval_contains
    (factorTwoPrimeResidualInterval_contains n)
  have he := factorTwoPrimeTaylorErrorInterval_contains
    (factorTwoPrimeCosTaylor_error (factorTwoPrimeResidual_abs_le n))
  have h := contains_add hp he
  unfold factorTwoPrimeReducedCosInterval
  convert h using 1
  ring

private theorem factorTwoPrimeReducedSinInterval_width_le (n : Fin 201) :
    width (factorTwoPrimeReducedSinInterval n) ≤
      (1 / 10000000000 : ℚ) := by
  rw [factorTwoPrimeReducedSinInterval, width_add]
  calc
    width (factorTwoPrimeSinTaylorInterval
          (factorTwoPrimeResidualInterval n)) +
        width factorTwoPrimeTaylorErrorInterval ≤
      (3 / 2 : ℚ) * (1 / 30000000000) +
        (1 / 70000000000 : ℚ) :=
      add_le_add
        (factorTwoPrimeSinTaylorInterval_width_le_structural
          (factorTwoPrimeResidualInterval_valid n)
          (factorTwoPrimeResidualInterval_absBound n)
          (factorTwoPrimeResidualInterval_width_le_structural n)
          (by norm_num))
        factorTwoPrimeTaylorErrorInterval_width_le
    _ ≤ (1 / 10000000000 : ℚ) := by norm_num

private theorem factorTwoPrimeReducedCosInterval_width_le (n : Fin 201) :
    width (factorTwoPrimeReducedCosInterval n) ≤
      (1 / 10000000000 : ℚ) := by
  rw [factorTwoPrimeReducedCosInterval, width_add]
  calc
    width (factorTwoPrimeCosTaylorInterval
          (factorTwoPrimeResidualInterval n)) +
        width factorTwoPrimeTaylorErrorInterval ≤
      (9 / 10 : ℚ) * (1 / 30000000000) +
        (1 / 70000000000 : ℚ) :=
      add_le_add
        (factorTwoPrimeCosTaylorInterval_width_le_structural
          (factorTwoPrimeResidualInterval_valid n)
          (factorTwoPrimeResidualInterval_absBound n)
          (factorTwoPrimeResidualInterval_width_le_structural n)
          (by norm_num))
        factorTwoPrimeTaylorErrorInterval_width_le
    _ ≤ (1 / 10000000000 : ℚ) := by norm_num

/-! ## Restore the quarter turns -/

private def quarterSin (q : ℕ) (s c : ℝ) : ℝ :=
  match q % 4 with
  | 0 => s
  | 1 => c
  | 2 => -s
  | _ => -c

private def quarterCos (q : ℕ) (s c : ℝ) : ℝ :=
  match q % 4 with
  | 0 => c
  | 1 => -s
  | 2 => -c
  | _ => s

private def quarterSinInterval
    (q : ℕ) (S C : RatInterval) : RatInterval :=
  match q % 4 with
  | 0 => S
  | 1 => C
  | 2 => -S
  | _ => -C

private def quarterCosInterval
    (q : ℕ) (S C : RatInterval) : RatInterval :=
  match q % 4 with
  | 0 => C
  | 1 => -S
  | 2 => -C
  | _ => S

private theorem width_neg (I : RatInterval) : width (-I) = width I := by
  change -I.lower - -I.upper = I.upper - I.lower
  ring

private theorem quarterSinInterval_width_le
    {q : ℕ} {S C : RatInterval} {w : ℚ}
    (hS : width S ≤ w) (hC : width C ≤ w) :
    width (quarterSinInterval q S C) ≤ w := by
  have hlt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  interval_cases h : q % 4
  · simpa [quarterSinInterval, h] using hS
  · simpa [quarterSinInterval, h] using hC
  · simpa [quarterSinInterval, h, width_neg] using hS
  · simpa [quarterSinInterval, h, width_neg] using hC

private theorem quarterCosInterval_width_le
    {q : ℕ} {S C : RatInterval} {w : ℚ}
    (hS : width S ≤ w) (hC : width C ≤ w) :
    width (quarterCosInterval q S C) ≤ w := by
  have hlt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  interval_cases h : q % 4
  · simpa [quarterCosInterval, h] using hC
  · simpa [quarterCosInterval, h, width_neg] using hS
  · simpa [quarterCosInterval, h, width_neg] using hC
  · simpa [quarterCosInterval, h] using hS

private theorem sin_add_nat_mul_pi_div_two (x : ℝ) (q : ℕ) :
    Real.sin (x + (q : ℝ) * Real.pi / 2) =
      quarterSin q (Real.sin x) (Real.cos x) := by
  have hd : q % 4 + 4 * (q / 4) = q := Nat.mod_add_div q 4
  have hdr : (q : ℝ) = (q % 4 : ℕ) + 4 * (q / 4 : ℕ) := by
    exact_mod_cast hd.symm
  have harg :
      x + (q : ℝ) * Real.pi / 2 =
        (x + (q % 4 : ℕ) * Real.pi / 2) +
          (q / 4 : ℕ) * (2 * Real.pi) := by
    rw [hdr]
    ring
  rw [harg, Real.sin_add_nat_mul_two_pi]
  have hlt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  interval_cases h : q % 4
  · simp [quarterSin, h]
  · simp [quarterSin, h, Real.sin_add_pi_div_two]
  · rw [show x + (2 : ℕ) * Real.pi / 2 = x + Real.pi by
      norm_num]
    simp [quarterSin, h]
  · rw [show x + (3 : ℕ) * Real.pi / 2 =
        (x + Real.pi) + Real.pi / 2 by
      ring_nf]
    simp [quarterSin, h, Real.sin_add_pi_div_two]

private theorem cos_add_nat_mul_pi_div_two (x : ℝ) (q : ℕ) :
    Real.cos (x + (q : ℝ) * Real.pi / 2) =
      quarterCos q (Real.sin x) (Real.cos x) := by
  have hd : q % 4 + 4 * (q / 4) = q := Nat.mod_add_div q 4
  have hdr : (q : ℝ) = (q % 4 : ℕ) + 4 * (q / 4 : ℕ) := by
    exact_mod_cast hd.symm
  have harg :
      x + (q : ℝ) * Real.pi / 2 =
        (x + (q % 4 : ℕ) * Real.pi / 2) +
          (q / 4 : ℕ) * (2 * Real.pi) := by
    rw [hdr]
    ring
  rw [harg, Real.cos_add_nat_mul_two_pi]
  have hlt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  interval_cases h : q % 4
  · simp [quarterCos, h]
  · simp [quarterCos, h, Real.cos_add_pi_div_two]
  · rw [show x + (2 : ℕ) * Real.pi / 2 = x + Real.pi by
      norm_num]
    simp [quarterCos, h]
  · rw [show x + (3 : ℕ) * Real.pi / 2 =
        (x + Real.pi) + Real.pi / 2 by
      ring_nf]
    simp [quarterCos, h, Real.cos_add_pi_div_two]

private theorem quarterSinInterval_contains
    {q : ℕ} {S C : RatInterval} {s c : ℝ}
    (hs : S.Contains s) (hc : C.Contains c) :
    (quarterSinInterval q S C).Contains (quarterSin q s c) := by
  have hlt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  interval_cases h : q % 4
  · simpa [quarterSinInterval, quarterSin, h] using hs
  · simpa [quarterSinInterval, quarterSin, h] using hc
  · simpa [quarterSinInterval, quarterSin, h] using contains_neg hs
  · simpa [quarterSinInterval, quarterSin, h] using contains_neg hc

private theorem quarterCosInterval_contains
    {q : ℕ} {S C : RatInterval} {s c : ℝ}
    (hs : S.Contains s) (hc : C.Contains c) :
    (quarterCosInterval q S C).Contains (quarterCos q s c) := by
  have hlt : q % 4 < 4 := Nat.mod_lt q (by norm_num)
  interval_cases h : q % 4
  · simpa [quarterCosInterval, quarterCos, h] using hc
  · simpa [quarterCosInterval, quarterCos, h] using contains_neg hs
  · simpa [quarterCosInterval, quarterCos, h] using contains_neg hc
  · simpa [quarterCosInterval, quarterCos, h] using hs

/-- Public exact rational enclosure of the retained-prime sine phase. -/
def factorTwoPrimeSinInterval (n : Fin 201) : RatInterval :=
  quarterSinInterval (factorTwoPrimeQuarterIndex n)
    (factorTwoPrimeReducedSinInterval n)
    (factorTwoPrimeReducedCosInterval n)

/-- Public exact rational enclosure of the retained-prime cosine phase. -/
def factorTwoPrimeCosInterval (n : Fin 201) : RatInterval :=
  quarterCosInterval (factorTwoPrimeQuarterIndex n)
    (factorTwoPrimeReducedSinInterval n)
    (factorTwoPrimeReducedCosInterval n)

theorem factorTwoPrimeSinInterval_contains (n : Fin 201) :
    (factorTwoPrimeSinInterval n).Contains
      (Real.sin (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) := by
  have h := quarterSinInterval_contains
    (q := factorTwoPrimeQuarterIndex n)
    (factorTwoPrimeReducedSinInterval_contains n)
    (factorTwoPrimeReducedCosInterval_contains n)
  rw [← sin_add_nat_mul_pi_div_two] at h
  unfold factorTwoPrimeSinInterval
  convert h using 1
  unfold factorTwoPrimeResidual
  ring

theorem factorTwoPrimeCosInterval_contains (n : Fin 201) :
    (factorTwoPrimeCosInterval n).Contains
      (Real.cos (2 * factorTwoMomentY n.1 * factorTwoPrimeShift)) := by
  have h := quarterCosInterval_contains
    (q := factorTwoPrimeQuarterIndex n)
    (factorTwoPrimeReducedSinInterval_contains n)
    (factorTwoPrimeReducedCosInterval_contains n)
  rw [← cos_add_nat_mul_pi_div_two] at h
  unfold factorTwoPrimeCosInterval
  convert h using 1
  unfold factorTwoPrimeResidual
  ring

/-! ## Structural width certificates -/

theorem factorTwoPrimeTrigIntervals_width_le :
    ∀ n : Fin 201,
      width (factorTwoPrimeSinInterval n) ≤ (1 / 10000000000 : ℚ) ∧
      width (factorTwoPrimeCosInterval n) ≤ (1 / 10000000000 : ℚ) := by
  intro n
  constructor
  · exact quarterSinInterval_width_le
      (factorTwoPrimeReducedSinInterval_width_le n)
      (factorTwoPrimeReducedCosInterval_width_le n)
  · exact quarterCosInterval_width_le
      (factorTwoPrimeReducedSinInterval_width_le n)
      (factorTwoPrimeReducedCosInterval_width_le n)

theorem factorTwoPrimeSinInterval_width_le (n : Fin 201) :
    width (factorTwoPrimeSinInterval n) ≤ (1 / 10000000000 : ℚ) :=
  (factorTwoPrimeTrigIntervals_width_le n).1

theorem factorTwoPrimeCosInterval_width_le (n : Fin 201) :
    width (factorTwoPrimeCosInterval n) ≤ (1 / 10000000000 : ℚ) :=
  (factorTwoPrimeTrigIntervals_width_le n).2

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeTrigEnclosures
