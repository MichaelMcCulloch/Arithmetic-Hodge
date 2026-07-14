import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaSineStructuralWidth

open RatInterval
open YoshidaSineMomentEnclosures

/-!
# Structural width bounds for the Yoshida sine parameters

These lemmas expose uniform rational estimates for the interval parameters in
the Cauchy-series formula.  They are deliberately independent of any finite
frequency cutoff: the dependence on the mode remains symbolic.
-/

/-- The scaled-frequency interval is a valid interval. -/
theorem yoshidaYInterval_valid (n : ℕ) :
    (yoshidaYInterval n).Valid :=
  valid_of_contains (yoshidaYInterval_contains n)

/-- Uniform lower growth of the scaled frequency. -/
theorem four_mul_nat_le_yoshidaYInterval_lower (n : ℕ) :
    4 * (n : ℚ) ≤ (yoshidaYInterval n).lower := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change 4 * (n : ℚ) ≤
    piFineInterval.lower * (n : ℚ) / logTwoFineInterval.upper
  have hc : (4 : ℚ) ≤
      piFineInterval.lower / logTwoFineInterval.upper := by
    norm_num [piFineInterval, logTwoFineInterval]
  calc
    4 * (n : ℚ) ≤
        (piFineInterval.lower / logTwoFineInterval.upper) * n :=
      mul_le_mul_of_nonneg_right hc hn
    _ = piFineInterval.lower * (n : ℚ) /
        logTwoFineInterval.upper := by ring

/-- A sharper lower slope used to control the Cauchy denominators. -/
theorem nine_halves_mul_nat_le_yoshidaYInterval_lower (n : ℕ) :
    (9 / 2 : ℚ) * n ≤ (yoshidaYInterval n).lower := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change (9 / 2 : ℚ) * (n : ℚ) ≤
    piFineInterval.lower * (n : ℚ) / logTwoFineInterval.upper
  have hc : (9 / 2 : ℚ) ≤
      piFineInterval.lower / logTwoFineInterval.upper := by
    norm_num [piFineInterval, logTwoFineInterval]
  calc
    (9 / 2 : ℚ) * (n : ℚ) ≤
        (piFineInterval.lower / logTwoFineInterval.upper) * n :=
      mul_le_mul_of_nonneg_right hc hn
    _ = piFineInterval.lower * (n : ℚ) /
        logTwoFineInterval.upper := by ring

/-- Uniform upper growth of the scaled frequency. -/
theorem yoshidaYInterval_upper_le_five_mul_nat (n : ℕ) :
    (yoshidaYInterval n).upper ≤ 5 * (n : ℚ) := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change piFineInterval.upper * (n : ℚ) /
      logTwoFineInterval.lower ≤ 5 * (n : ℚ)
  have hc : piFineInterval.upper / logTwoFineInterval.lower ≤ (5 : ℚ) := by
    norm_num [piFineInterval, logTwoFineInterval]
  calc
    piFineInterval.upper * (n : ℚ) / logTwoFineInterval.lower =
        (piFineInterval.upper / logTwoFineInterval.lower) * n := by ring
    _ ≤ 5 * (n : ℚ) := mul_le_mul_of_nonneg_right hc hn

/-- A sharper upper slope for numerator and square-width estimates. -/
theorem yoshidaYInterval_upper_le_ninety_one_twentieths_mul_nat (n : ℕ) :
    (yoshidaYInterval n).upper ≤ (91 / 20 : ℚ) * n := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change piFineInterval.upper * (n : ℚ) /
      logTwoFineInterval.lower ≤ (91 / 20 : ℚ) * (n : ℚ)
  have hc : piFineInterval.upper / logTwoFineInterval.lower ≤
      (91 / 20 : ℚ) := by
    norm_num [piFineInterval, logTwoFineInterval]
  calc
    piFineInterval.upper * (n : ℚ) / logTwoFineInterval.lower =
        (piFineInterval.upper / logTwoFineInterval.lower) * n := by ring
    _ ≤ (91 / 20 : ℚ) * n := mul_le_mul_of_nonneg_right hc hn

/-- The uncertainty in `pi*n/log 2` is linear in the mode with a uniform
coefficient below `1/7e9`. -/
theorem yoshidaYInterval_width_le (n : ℕ) :
    width (yoshidaYInterval n) ≤ (n : ℚ) / 7000000000 := by
  have hn : (0 : ℚ) ≤ n := by positivity
  change
    piFineInterval.upper * (n : ℚ) / logTwoFineInterval.lower -
        piFineInterval.lower * (n : ℚ) / logTwoFineInterval.upper ≤
      (n : ℚ) / 7000000000
  have hc :
      piFineInterval.upper / logTwoFineInterval.lower -
          piFineInterval.lower / logTwoFineInterval.upper ≤
        (1 : ℚ) / 7000000000 := by
    norm_num [piFineInterval, logTwoFineInterval]
  calc
    piFineInterval.upper * (n : ℚ) / logTwoFineInterval.lower -
          piFineInterval.lower * (n : ℚ) / logTwoFineInterval.upper =
        (piFineInterval.upper / logTwoFineInterval.lower -
          piFineInterval.lower / logTwoFineInterval.upper) * n := by ring
    _ ≤ ((1 : ℚ) / 7000000000) * n :=
      mul_le_mul_of_nonneg_right hc hn
    _ = (n : ℚ) / 7000000000 := by ring

/-- The scaled-frequency interval is nonnegative. -/
theorem yoshidaYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (yoshidaYInterval n).lower := by
  exact (by positivity : (0 : ℚ) ≤ (9 / 2 : ℚ) * n).trans
    (nine_halves_mul_nat_le_yoshidaYInterval_lower n)

/-- Symmetric magnitude bound for the scaled-frequency interval. -/
theorem yoshidaYInterval_absBound (n : ℕ) :
    (yoshidaYInterval n).AbsBound ((91 / 20 : ℚ) * n) := by
  constructor
  · exact (neg_nonpos.mpr (by positivity)).trans
      (yoshidaYInterval_lower_nonneg n)
  · exact yoshidaYInterval_upper_le_ninety_one_twentieths_mul_nat n

/-- Squaring the nonnegative frequency interval preserves validity. -/
theorem nonnegSquare_yoshidaYInterval_valid (n : ℕ) :
    (nonnegSquare (yoshidaYInterval n)).Valid := by
  change (yoshidaYInterval n).lower ^ 2 ≤
    (yoshidaYInterval n).upper ^ 2
  exact pow_le_pow_left₀ (yoshidaYInterval_lower_nonneg n)
    (yoshidaYInterval_valid n) 2

/-- Structural width bound for the squared frequency interval. -/
theorem nonnegSquare_yoshidaYInterval_width_le (n : ℕ) :
    width (nonnegSquare (yoshidaYInterval n)) ≤
      13 * (n : ℚ) ^ 2 / 10000000000 := by
  have hn : (0 : ℚ) ≤ n := by positivity
  have hwidth := yoshidaYInterval_width_le n
  have hsum :
      (yoshidaYInterval n).upper + (yoshidaYInterval n).lower ≤
        (91 / 10 : ℚ) * n := by
    calc
      (yoshidaYInterval n).upper + (yoshidaYInterval n).lower ≤
          (yoshidaYInterval n).upper + (yoshidaYInterval n).upper :=
        by simpa only [add_comm] using
          (add_le_add_left (yoshidaYInterval_valid n)
            (yoshidaYInterval n).upper)
      _ ≤ (91 / 20 : ℚ) * n + (91 / 20 : ℚ) * n :=
        add_le_add
          (yoshidaYInterval_upper_le_ninety_one_twentieths_mul_nat n)
          (yoshidaYInterval_upper_le_ninety_one_twentieths_mul_nat n)
      _ = (91 / 10 : ℚ) * n := by ring
  change
    (yoshidaYInterval n).upper ^ 2 -
        (yoshidaYInterval n).lower ^ 2 ≤
      13 * (n : ℚ) ^ 2 / 10000000000
  rw [sq_sub_sq]
  calc
    ((yoshidaYInterval n).upper + (yoshidaYInterval n).lower) *
          ((yoshidaYInterval n).upper - (yoshidaYInterval n).lower) ≤
        ((91 / 10 : ℚ) * n) * ((n : ℚ) / 7000000000) := by
      exact mul_le_mul hsum hwidth
        (width_nonneg (yoshidaYInterval_valid n)) (by positivity)
    _ ≤ 13 * (n : ℚ) ^ 2 / 10000000000 := by
      have hcoeff :
          ((1 : ℚ) / 7000000000) * (91 / 10) ≤
            13 / 10000000000 := by norm_num
      nlinarith [sq_nonneg (n : ℚ)]

/-- The square-root enclosure is valid. -/
theorem sqrtTwoInterval_valid : sqrtTwoInterval.Valid :=
  valid_of_contains sqrtTwoInterval_contains

/-- Exact width of the square-root enclosure. -/
theorem sqrtTwoInterval_width :
    width sqrtTwoInterval = (1 : ℚ) / 1000000000000000 := by
  norm_num [width, sqrtTwoInterval]

/-- A simple positive floor for the square-root enclosure. -/
theorem one_le_sqrtTwoInterval_lower :
    (1 : ℚ) ≤ sqrtTwoInterval.lower := by
  norm_num [sqrtTwoInterval]

/-- Reciprocal uncertainty in the square-root enclosure is no larger than
the original `10^-15` uncertainty. -/
theorem sqrtTwoInterval_inv_width_le :
    width sqrtTwoInterval⁻¹ ≤ (1 : ℚ) / 1000000000000000 := by
  calc
    width sqrtTwoInterval⁻¹ ≤
        width sqrtTwoInterval / ((1 : ℚ) * 1) :=
      width_inv_le_of_lower sqrtTwoInterval_valid (by norm_num)
        one_le_sqrtTwoInterval_lower
    _ = (1 : ℚ) / 1000000000000000 := by
      rw [sqrtTwoInterval_width]
      ring

/-- The dyadic coefficient `1 - 1/(sqrt 2 * 4^k)` is a valid nonnegative
interval bounded by one. -/
theorem sineDyadicFactor_valid_absBound (k : ℕ) :
    let F := RatInterval.pure 1 - sqrtTwoInterval⁻¹ /
      RatInterval.pure ((4 : ℚ) ^ k)
    F.Valid ∧ F.AbsBound 1 := by
  dsimp only
  have hpow : (0 : ℚ) < (4 : ℚ) ^ k := by positivity
  have hInvValid := valid_inv_of_pos sqrtTwoInterval_valid
    (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower)
  have hDivValid := valid_div_of_pos hInvValid (valid_pure _)
    (by change 0 < (4 : ℚ) ^ k; exact hpow)
  constructor
  · exact valid_sub (valid_pure 1) hDivValid
  · have hInvNonneg : 0 ≤ sqrtTwoInterval⁻¹.lower := by
      change 0 ≤ sqrtTwoInterval.upper⁻¹
      norm_num [sqrtTwoInterval]
    have hInvAbs : sqrtTwoInterval⁻¹.AbsBound 1 :=
      by simpa only [inv_one] using
        (absBound_inv_of_lower sqrtTwoInterval_valid (by norm_num)
          one_le_sqrtTwoInterval_lower)
    have hPowLower :
        (1 : ℚ) ≤ (RatInterval.pure ((4 : ℚ) ^ k)).lower := by
      change (1 : ℚ) ≤ (4 : ℚ) ^ k
      exact one_le_pow₀ (by norm_num)
    have hDivAbs :
        (sqrtTwoInterval⁻¹ /
          RatInterval.pure ((4 : ℚ) ^ k)).AbsBound 1 := by
      simpa using absBound_div_of_lower hInvValid (valid_pure _)
        hInvAbs (by norm_num : (0 : ℚ) ≤ 1) (by norm_num : (0 : ℚ) < 1)
        hPowLower
    have hDivLower :
        0 ≤ (sqrtTwoInterval⁻¹ /
          RatInterval.pure ((4 : ℚ) ^ k)).lower := by
      change 0 ≤ (sqrtTwoInterval⁻¹ *
        (RatInterval.pure ((4 : ℚ) ^ k))⁻¹).lower
      exact mul_lower_nonneg_of_nonneg hInvNonneg (by
        change 0 ≤ ((4 : ℚ) ^ k)⁻¹
        positivity) hInvValid (valid_inv_of_pos (valid_pure _) (by
          change 0 < (4 : ℚ) ^ k
          exact hpow))
    have hDivUpper :
        (sqrtTwoInterval⁻¹ /
          RatInterval.pure ((4 : ℚ) ^ k)).upper ≤ 1 := hDivAbs.2
    unfold AbsBound
    change -(1 : ℚ) ≤ 1 -
        (sqrtTwoInterval⁻¹ /
          RatInterval.pure ((4 : ℚ) ^ k)).upper ∧
      1 - (sqrtTwoInterval⁻¹ /
        RatInterval.pure ((4 : ℚ) ^ k)).lower ≤ 1
    constructor <;> linarith

/-- The dyadic-factor width is uniformly at most `10^-15`. -/
theorem sineDyadicFactor_width_le (k : ℕ) :
    width (RatInterval.pure 1 - sqrtTwoInterval⁻¹ /
      RatInterval.pure ((4 : ℚ) ^ k)) ≤
      (1 : ℚ) / 1000000000000000 := by
  rw [width_sub, width_pure, zero_add]
  change width (sqrtTwoInterval⁻¹ *
    (RatInterval.pure ((4 : ℚ) ^ k))⁻¹) ≤ _
  rw [show (RatInterval.pure ((4 : ℚ) ^ k))⁻¹ =
      RatInterval.pure (((4 : ℚ) ^ k)⁻¹) by rfl,
    width_mul_pure _ (valid_inv_of_pos sqrtTwoInterval_valid
      (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower))]
  rw [abs_of_nonneg (by positivity)]
  calc
    ((4 : ℚ) ^ k)⁻¹ * width sqrtTwoInterval⁻¹ ≤
        1 * width sqrtTwoInterval⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact (inv_le_one₀ (by positivity :
          (0 : ℚ) < (4 : ℚ) ^ k)).2 (one_le_pow₀ (by norm_num))
      · exact width_nonneg (valid_inv_of_pos sqrtTwoInterval_valid
          (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower))
    _ ≤ (1 : ℚ) / 1000000000000000 := by
      simpa using sqrtTwoInterval_inv_width_le

/-! ## One Cauchy summand -/

/-- Numerator interval in one scaled Cauchy summand. -/
def sineCauchyNumeratorInterval (n k : ℕ) : RatInterval :=
  yoshidaYInterval n *
    (RatInterval.pure 1 - sqrtTwoInterval⁻¹ /
      RatInterval.pure ((4 : ℚ) ^ k))

/-- Symbolic positive floor for the corresponding denominator. -/
def sineCauchyDenominatorFloor (n k : ℕ) : ℚ :=
  ((k : ℚ) + 1 / 4) ^ 2 + ((9 / 2 : ℚ) * n) ^ 2

theorem sineCauchyNumeratorInterval_valid (n k : ℕ) :
    (sineCauchyNumeratorInterval n k).Valid := by
  exact valid_mul (yoshidaYInterval_valid n)
    (sineDyadicFactor_valid_absBound k).1

theorem sineCauchyNumeratorInterval_absBound (n k : ℕ) :
    (sineCauchyNumeratorInterval n k).AbsBound
      ((91 / 20 : ℚ) * n) := by
  simpa [sineCauchyNumeratorInterval] using
    (absBound_mul (yoshidaYInterval_valid n)
      (sineDyadicFactor_valid_absBound k).1
      (yoshidaYInterval_absBound n)
      (sineDyadicFactor_valid_absBound k).2 (by positivity) (by norm_num))

/-- The numerator uncertainty is still linear in the mode. -/
theorem sineCauchyNumeratorInterval_width_le (n k : ℕ) :
    width (sineCauchyNumeratorInterval n k) ≤
      (n : ℚ) / 6900000000 := by
  have hmul := width_mul_le (yoshidaYInterval_valid n)
    (sineDyadicFactor_valid_absBound k).1
    (yoshidaYInterval_absBound n)
    (sineDyadicFactor_valid_absBound k).2 (by positivity) (by norm_num)
  have hright :
      (91 / 20 : ℚ) * n * width
          (RatInterval.pure 1 - sqrtTwoInterval⁻¹ /
            RatInterval.pure ((4 : ℚ) ^ k)) ≤
        (91 / 20 : ℚ) * n * ((1 : ℚ) / 1000000000000000) := by
    exact mul_le_mul_of_nonneg_left (sineDyadicFactor_width_le k) (by positivity)
  calc
    width (sineCauchyNumeratorInterval n k) ≤
        1 * width (yoshidaYInterval n) +
          (91 / 20 : ℚ) * n * width
            (RatInterval.pure 1 - sqrtTwoInterval⁻¹ /
              RatInterval.pure ((4 : ℚ) ^ k)) := by
      simpa only [sineCauchyNumeratorInterval] using hmul
    _ ≤ 1 * ((n : ℚ) / 7000000000) +
        (91 / 20 : ℚ) * n * ((1 : ℚ) / 1000000000000000) :=
      add_le_add (mul_le_mul_of_nonneg_left (yoshidaYInterval_width_le n)
        (by norm_num)) hright
    _ ≤ (n : ℚ) / 6900000000 := by
      have hn : (0 : ℚ) ≤ n := by positivity
      nlinarith

theorem cauchyDenomInterval_valid (n k : ℕ) :
    (cauchyDenomInterval n k).Valid := by
  exact valid_add (valid_pure _)
    (nonnegSquare_yoshidaYInterval_valid n)

theorem sineCauchyDenominatorFloor_pos
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    0 < sineCauchyDenominatorFloor n k := by
  unfold sineCauchyDenominatorFloor
  have hn0 : (0 : ℚ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  positivity

theorem sineCauchyDenominatorFloor_le_lower
    (n k : ℕ) :
    sineCauchyDenominatorFloor n k ≤
      (cauchyDenomInterval n k).lower := by
  unfold sineCauchyDenominatorFloor
  change ((k : ℚ) + 1 / 4) ^ 2 + ((9 / 2 : ℚ) * n) ^ 2 ≤
    quarterShiftQ k ^ 2 + (yoshidaYInterval n).lower ^ 2
  unfold quarterShiftQ
  have hlo := nine_halves_mul_nat_le_yoshidaYInterval_lower n
  have hbase : (0 : ℚ) ≤ (9 / 2 : ℚ) * n := by positivity
  have hsq := pow_le_pow_left₀ hbase hlo 2
  norm_num only
  simpa only [add_comm] using
    (add_le_add_left hsq (((k : ℚ) + 1 / 4) ^ 2))

theorem cauchyDenomInterval_width_le (n k : ℕ) :
    width (cauchyDenomInterval n k) ≤
      13 * (n : ℚ) ^ 2 / 10000000000 := by
  rw [show cauchyDenomInterval n k =
      RatInterval.pure (quarterShiftQ k ^ 2) +
        nonnegSquare (yoshidaYInterval n) by rfl,
    width_add, width_pure, zero_add]
  exact nonnegSquare_yoshidaYInterval_width_le n

private theorem sineCauchyTerm_width_budget
    {n : ℕ} (hn : 1 ≤ n) {m : ℚ}
    (hm : 0 < m) (hmn : ((9 / 2 : ℚ) * n) ^ 2 ≤ m) :
    m⁻¹ * ((n : ℚ) / 6900000000) +
        ((91 / 20 : ℚ) * n) *
          ((13 * (n : ℚ) ^ 2 / 10000000000) / (m * m)) ≤
      ((n : ℚ) / 2250000000) * m⁻¹ := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  field_simp [hm.ne']
  nlinarith [sq_nonneg (n : ℚ), sq_nonneg (m - ((9 / 2 : ℚ) * n) ^ 2)]

/-- Uniform structural uncertainty of a scaled Cauchy summand. -/
theorem scaledSineCauchyTermInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    width (scaledSineCauchyTermInterval n k) ≤
      ((n : ℚ) / 2250000000) *
        (sineCauchyDenominatorFloor n k)⁻¹ := by
  let m := sineCauchyDenominatorFloor n k
  have hm : 0 < m := sineCauchyDenominatorFloor_pos hn k
  have hfloor := sineCauchyDenominatorFloor_le_lower n k
  have hdiv := width_div_le_of_lower
    (sineCauchyNumeratorInterval_valid n k)
    (cauchyDenomInterval_valid n k)
    (sineCauchyNumeratorInterval_absBound n k) (by positivity) hm hfloor
  have hnum := sineCauchyNumeratorInterval_width_le n k
  have hden := cauchyDenomInterval_width_le n k
  have hfirst :
      m⁻¹ * width (sineCauchyNumeratorInterval n k) ≤
        m⁻¹ * ((n : ℚ) / 6900000000) :=
    mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hm.le)
  have hsecond :
      ((91 / 20 : ℚ) * n) *
          (width (cauchyDenomInterval n k) / (m * m)) ≤
        ((91 / 20 : ℚ) * n) *
          ((13 * (n : ℚ) ^ 2 / 10000000000) / (m * m)) := by
    apply mul_le_mul_of_nonneg_left
    · exact div_le_div_of_nonneg_right hden (mul_nonneg hm.le hm.le)
    · positivity
  have hmBase : ((9 / 2 : ℚ) * n) ^ 2 ≤ m := by
    dsimp only [m, sineCauchyDenominatorFloor]
    exact le_add_of_nonneg_left (sq_nonneg ((k : ℚ) + 1 / 4))
  change width (sineCauchyNumeratorInterval n k / cauchyDenomInterval n k) ≤ _
  calc
    width (sineCauchyNumeratorInterval n k / cauchyDenomInterval n k) ≤
        m⁻¹ * width (sineCauchyNumeratorInterval n k) +
          ((91 / 20 : ℚ) * n) *
            (width (cauchyDenomInterval n k) / (m * m)) := hdiv
    _ ≤ m⁻¹ * ((n : ℚ) / 6900000000) +
        ((91 / 20 : ℚ) * n) *
          ((13 * (n : ℚ) ^ 2 / 10000000000) / (m * m)) :=
      add_le_add hfirst hsecond
    _ ≤ ((n : ℚ) / 2250000000) * m⁻¹ :=
      sineCauchyTerm_width_budget hn hm hmBase

/-! ## Polar term -/

/-- Constant coefficient in the scaled sine polar term. -/
def sinePolarCoefficientInterval : RatInterval :=
  RatInterval.pure 2 - sqrtTwoInterval - sqrtTwoInterval⁻¹

theorem sinePolarCoefficientInterval_valid :
    sinePolarCoefficientInterval.Valid := by
  exact valid_sub (valid_sub (valid_pure 2) sqrtTwoInterval_valid)
    (valid_inv_of_pos sqrtTwoInterval_valid
      (lt_of_lt_of_le (by norm_num) one_le_sqrtTwoInterval_lower))

theorem sinePolarCoefficientInterval_absBound :
    sinePolarCoefficientInterval.AbsBound (1 / 4 : ℚ) := by
  change
    -(1 / 4 : ℚ) ≤
        2 - sqrtTwoInterval.upper - sqrtTwoInterval.lower⁻¹ ∧
      2 - sqrtTwoInterval.lower - sqrtTwoInterval.upper⁻¹ ≤
        (1 / 4 : ℚ)
  norm_num [sqrtTwoInterval]

theorem sinePolarCoefficientInterval_width_le :
    width sinePolarCoefficientInterval ≤
      (2 : ℚ) / 1000000000000000 := by
  unfold sinePolarCoefficientInterval
  rw [width_sub, width_sub, width_pure, zero_add]
  calc
    width sqrtTwoInterval + width sqrtTwoInterval⁻¹ ≤
        (1 : ℚ) / 1000000000000000 +
          (1 : ℚ) / 1000000000000000 :=
      add_le_add sqrtTwoInterval_width.le sqrtTwoInterval_inv_width_le
    _ = (2 : ℚ) / 1000000000000000 := by ring

def sinePolarNumeratorInterval (n : ℕ) : RatInterval :=
  RatInterval.pure 4 * yoshidaYInterval n * sinePolarCoefficientInterval

theorem sinePolarNumeratorInterval_valid (n : ℕ) :
    (sinePolarNumeratorInterval n).Valid := by
  exact valid_mul
    (valid_mul (valid_pure 4) (yoshidaYInterval_valid n))
    sinePolarCoefficientInterval_valid

private theorem four_mul_yoshidaYInterval_absBound (n : ℕ) :
    (RatInterval.pure 4 * yoshidaYInterval n).AbsBound
      ((91 / 5 : ℚ) * n) := by
  convert absBound_mul (valid_pure 4) (yoshidaYInterval_valid n)
    (absBound_pure (by norm_num : |(4 : ℚ)| ≤ 4))
    (yoshidaYInterval_absBound n) (by norm_num) (by positivity) using 1
  ring

theorem sinePolarNumeratorInterval_absBound (n : ℕ) :
    (sinePolarNumeratorInterval n).AbsBound ((91 / 20 : ℚ) * n) := by
  unfold sinePolarNumeratorInterval
  convert
    (absBound_mul (valid_mul (valid_pure 4) (yoshidaYInterval_valid n))
      sinePolarCoefficientInterval_valid
      (four_mul_yoshidaYInterval_absBound n)
      sinePolarCoefficientInterval_absBound (by positivity) (by norm_num)) using 1
  ring

theorem sinePolarNumeratorInterval_width_le (n : ℕ) :
    width (sinePolarNumeratorInterval n) ≤ (n : ℚ) / 6900000000 := by
  have hFourWidth :
      width (RatInterval.pure 4 * yoshidaYInterval n) =
        4 * width (yoshidaYInterval n) := by
    rw [width_pure_mul 4 (yoshidaYInterval_valid n), abs_of_nonneg (by norm_num)]
  have hmul := width_mul_le
    (valid_mul (valid_pure 4) (yoshidaYInterval_valid n))
    sinePolarCoefficientInterval_valid
    (four_mul_yoshidaYInterval_absBound n)
    sinePolarCoefficientInterval_absBound (by positivity) (by norm_num)
  calc
    width (sinePolarNumeratorInterval n) ≤
        (1 / 4 : ℚ) * width (RatInterval.pure 4 * yoshidaYInterval n) +
          ((91 / 5 : ℚ) * n) * width sinePolarCoefficientInterval := by
      simpa only [sinePolarNumeratorInterval] using hmul
    _ ≤ (1 / 4 : ℚ) * (4 * ((n : ℚ) / 7000000000)) +
          ((91 / 5 : ℚ) * n) *
            ((2 : ℚ) / 1000000000000000) := by
      apply add_le_add
      · rw [hFourWidth]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (yoshidaYInterval_width_le n)
            (by norm_num)) (by norm_num)
      · exact mul_le_mul_of_nonneg_left
          sinePolarCoefficientInterval_width_le (by positivity)
    _ ≤ (n : ℚ) / 6900000000 := by
      have hn : (0 : ℚ) ≤ n := by positivity
      nlinarith

theorem polarDenomInterval_valid (n : ℕ) :
    (polarDenomInterval n).Valid := by
  change 1 / 4 + 4 * (yoshidaYInterval n).lower ^ 2 ≤
    1 / 4 + 4 * (yoshidaYInterval n).upper ^ 2
  have hsq := pow_le_pow_left₀ (yoshidaYInterval_lower_nonneg n)
    (yoshidaYInterval_valid n) 2
  simpa only [add_comm] using
    (add_le_add_left
      (mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℚ) ≤ 4))
      (1 / 4 : ℚ))

theorem polarDenomInterval_floor_le_lower (n : ℕ) :
    81 * (n : ℚ) ^ 2 ≤ (polarDenomInterval n).lower := by
  change 81 * (n : ℚ) ^ 2 ≤
    1 / 4 + 4 * (yoshidaYInterval n).lower ^ 2
  have hlo := nine_halves_mul_nat_le_yoshidaYInterval_lower n
  have hsq := pow_le_pow_left₀ (by positivity :
    (0 : ℚ) ≤ (9 / 2 : ℚ) * n) hlo 2
  nlinarith

theorem polarDenomInterval_width_le (n : ℕ) :
    width (polarDenomInterval n) ≤
      52 * (n : ℚ) ^ 2 / 10000000000 := by
  have hsq := nonnegSquare_yoshidaYInterval_width_le n
  change
    (1 / 4 + 4 * (yoshidaYInterval n).upper ^ 2) -
        (1 / 4 + 4 * (yoshidaYInterval n).lower ^ 2) ≤
      52 * (n : ℚ) ^ 2 / 10000000000
  calc
    (1 / 4 + 4 * (yoshidaYInterval n).upper ^ 2) -
        (1 / 4 + 4 * (yoshidaYInterval n).lower ^ 2) =
      4 * width (nonnegSquare (yoshidaYInterval n)) := by
        unfold width nonnegSquare
        ring
    _ ≤ 4 * (13 * (n : ℚ) ^ 2 / 10000000000) :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 52 * (n : ℚ) ^ 2 / 10000000000 := by ring

/-- The polar interval contributes negligible structural width. -/
theorem sinePolarInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (sinePolarInterval n) ≤ (1 : ℚ) / 100000000000 := by
  let m : ℚ := 81 * (n : ℚ) ^ 2
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℚ) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hnQ)
  have hm : 0 < m := by dsimp only [m]; positivity
  have hdiv := width_div_le_of_lower
    (sinePolarNumeratorInterval_valid n) (polarDenomInterval_valid n)
    (sinePolarNumeratorInterval_absBound n) (by positivity) hm
    (polarDenomInterval_floor_le_lower n)
  have hfirst := mul_le_mul_of_nonneg_left
    (sinePolarNumeratorInterval_width_le n) (inv_nonneg.mpr hm.le)
  have hsecond :
      ((91 / 20 : ℚ) * n) *
          (width (polarDenomInterval n) / (m * m)) ≤
        ((91 / 20 : ℚ) * n) *
          ((52 * (n : ℚ) ^ 2 / 10000000000) / (m * m)) := by
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (polarDenomInterval_width_le n)
        (mul_nonneg hm.le hm.le)) (by positivity)
  have hbudget :
      m⁻¹ * ((n : ℚ) / 6900000000) +
          ((91 / 20 : ℚ) * n) *
            ((52 * (n : ℚ) ^ 2 / 10000000000) / (m * m)) ≤
        (1 : ℚ) / 100000000000 := by
    let C : ℚ :=
      1 / (81 * 6900000000) +
        ((91 / 20 : ℚ) * 52) / (81 ^ 2 * 10000000000)
    have heq :
        m⁻¹ * ((n : ℚ) / 6900000000) +
            ((91 / 20 : ℚ) * n) *
              ((52 * (n : ℚ) ^ 2 / 10000000000) / (m * m)) =
          C * (n : ℚ)⁻¹ := by
      dsimp only [m, C]
      field_simp [hn0]
    rw [heq]
    calc
      C * (n : ℚ)⁻¹ ≤ C * 1 := by
        apply mul_le_mul_of_nonneg_left
        · exact (inv_le_one₀ (lt_of_lt_of_le (by norm_num) hnQ)).2 hnQ
        · dsimp only [C]
          positivity
      _ ≤ (1 : ℚ) / 100000000000 := by
        dsimp only [C]
        norm_num
  change width (sinePolarNumeratorInterval n / polarDenomInterval n) ≤ _
  calc
    width (sinePolarNumeratorInterval n / polarDenomInterval n) ≤
        m⁻¹ * width (sinePolarNumeratorInterval n) +
          ((91 / 20 : ℚ) * n) *
            (width (polarDenomInterval n) / (m * m)) := hdiv
    _ ≤ m⁻¹ * ((n : ℚ) / 6900000000) +
          ((91 / 20 : ℚ) * n) *
            ((52 * (n : ℚ) ^ 2 / 10000000000) / (m * m)) :=
      add_le_add hfirst hsecond
    _ ≤ (1 : ℚ) / 100000000000 := hbudget

end ArithmeticHodge.Analysis.YoshidaSineStructuralWidth
