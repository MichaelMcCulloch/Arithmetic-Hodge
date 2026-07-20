import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaDiagonalDigammaHighBound
import ArithmeticHodge.Analysis.YoshidaDiagonalUniformDerivativeBound
import ArithmeticHodge.Analysis.YoshidaDiagonalUniformQBounds
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures

set_option autoImplicit false
set_option maxRecDepth 100000

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoCleanHighDiagonalEnclosures

noncomputable section

open ArithmeticHodge.Analysis
open DigammaTrapezoid
open RatInterval
open YoshidaDiagonalDigammaHighBound
open YoshidaDiagonalSeriesTail
open YoshidaDiagonalUniformDerivativeBound
open YoshidaDiagonalUniformIdentity
open YoshidaDiagonalUniformQBounds
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

/-!
# Clean high-frequency diagonal enclosures

The uniform diagonal identity separates three analytic remainders whose
combined width is fourth order in the mode.  The main term is evaluated
directly with fine rational intervals; in particular, this module does not
pass through the mode-independent `fineDiagonalBaseInterval`.
-/

private def highLogTwoInterval : RatInterval :=
  ⟨69314718055994 / 100000000000000,
    69314718055995 / 100000000000000⟩

private def logRatioLower (x : ℚ) : ℚ :=
  2 * ∑ i ∈ Finset.range 18, x ^ (2 * i + 1) / (2 * i + 1)

private def logRatioUpper (x : ℚ) : ℚ :=
  logRatioLower x + 2 * x ^ 37 / (1 - x ^ 2)

private def logRatioInterval (x : ℚ) : RatInterval :=
  ⟨logRatioLower x, logRatioUpper x⟩

private theorem logRatioInterval_contains
    {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (logRatioInterval x).Contains
      (Real.log ((((1 + x) / (1 - x) : ℚ) : ℝ))) := by
  have hx0R : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx0
  have hx1R : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hlo := Real.sum_range_le_log_div hx0R hx1R 18
  have hup := Real.log_div_le_sum_range_add hx0R hx1R 18
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
      _ ≤ 2 * ((∑ i ∈ Finset.range 18,
          (x : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
          (x : ℝ) ^ 37 / (1 - (x : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hup (by norm_num)
      _ = _ := by ring

private theorem highLogTwoInterval_contains :
    highLogTwoInterval.Contains yoshidaLength := by
  have hlo := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 18
  have hup := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 18
  constructor <;>
    norm_num [highLogTwoInterval, yoshidaLength,
      Finset.sum_range_succ] at hlo hup ⊢ <;> linarith

private def highLogNatRatioInterval (n : ℕ) : RatInterval :=
  if n ≤ 128 then
    -(logRatioInterval
      (((128 - n : ℕ) : ℚ) / ((128 + n : ℕ) : ℚ)))
  else
    logRatioInterval
      (((n - 128 : ℕ) : ℚ) / ((n + 128 : ℕ) : ℚ))

private def highLogNatInterval (n : ℕ) : RatInterval :=
  pure 7 * highLogTwoInterval + highLogNatRatioInterval n

private theorem highLogNatRatioInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highLogNatRatioInterval n).Contains
      (Real.log (n : ℝ) - 7 * yoshidaLength) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlogn : Real.log (n : ℝ) =
      Real.log ((n : ℝ) / 128) + 7 * yoshidaLength := by
    rw [Real.log_div (by positivity) (by norm_num)]
    have h128 : Real.log (128 : ℝ) = 7 * yoshidaLength := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      rfl
    rw [h128]
    ring
  unfold highLogNatRatioInterval
  split_ifs with hn128
  · let x : ℚ := ((128 - n : ℕ) : ℚ) / ((128 + n : ℕ) : ℚ)
    have hx0 : 0 ≤ x := by
      dsimp only [x]
      positivity
    have hx1 : x < 1 := by
      dsimp only [x]
      rw [div_lt_one (by positivity)]
      exact_mod_cast (by omega : 128 - n < 128 + n)
    have hx := logRatioInterval_contains hx0 hx1
    have hratio : ((((1 + x) / (1 - x) : ℚ) : ℝ)) =
        128 / (n : ℝ) := by
      dsimp only [x]
      norm_num only [Rat.cast_div, Rat.cast_natCast, Rat.cast_add,
        Rat.cast_sub, Rat.cast_ofNat]
      rw [Nat.cast_sub hn128]
      push_cast
      field_simp [ne_of_gt hnR]
      ring
    have hlogRatio :
        Real.log ((((1 + x) / (1 - x) : ℚ) : ℝ)) =
          -(Real.log (n : ℝ) - 7 * yoshidaLength) := by
      rw [hratio, Real.log_div (by norm_num) (by positivity)]
      rw [show Real.log (128 : ℝ) = 7 * yoshidaLength by
        rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
        rfl]
      ring
    have htarget : Real.log (n : ℝ) - 7 * yoshidaLength =
        -Real.log ((((1 + x) / (1 - x) : ℚ) : ℝ)) := by
      rw [hlogRatio]
      ring
    simpa only [x, htarget] using contains_neg hx
  · have hn128' : 128 ≤ n := by omega
    let x : ℚ := ((n - 128 : ℕ) : ℚ) / ((n + 128 : ℕ) : ℚ)
    have hx0 : 0 ≤ x := by
      dsimp only [x]
      positivity
    have hx1 : x < 1 := by
      dsimp only [x]
      rw [div_lt_one (by positivity)]
      exact_mod_cast (by omega : n - 128 < n + 128)
    have hx := logRatioInterval_contains hx0 hx1
    have hratio : ((((1 + x) / (1 - x) : ℚ) : ℝ)) =
        (n : ℝ) / 128 := by
      dsimp only [x]
      norm_num only [Rat.cast_div, Rat.cast_natCast, Rat.cast_add,
        Rat.cast_sub, Rat.cast_ofNat]
      rw [Nat.cast_sub hn128']
      push_cast
      field_simp
      ring
    rw [hratio] at hx
    have htarget : Real.log (n : ℝ) - 7 * yoshidaLength =
        Real.log ((n : ℝ) / 128) := by linarith
    simpa only [x, htarget] using hx

private theorem highLogNatInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highLogNatInterval n).Contains (Real.log (n : ℝ)) := by
  have hseven : (pure 7 * highLogTwoInterval).Contains
      (7 * yoshidaLength) :=
    contains_mul (contains_pure 7) highLogTwoInterval_contains
  have hratio := highLogNatRatioInterval_contains hn
  unfold highLogNatInterval
  convert contains_add hseven hratio using 1
  ring

private def negLogLengthInterval : RatInterval :=
  let xLower :=
    (1 - highLogTwoInterval.upper) / (1 + highLogTwoInterval.upper)
  let xUpper :=
    (1 - highLogTwoInterval.lower) / (1 + highLogTwoInterval.lower)
  ⟨logRatioLower xLower, logRatioUpper xUpper⟩

private theorem negLogLengthInterval_contains :
    negLogLengthInterval.Contains (-Real.log yoshidaLength) := by
  let xLower : ℚ :=
    (1 - highLogTwoInterval.upper) / (1 + highLogTwoInterval.upper)
  let xUpper : ℚ :=
    (1 - highLogTwoInterval.lower) / (1 + highLogTwoInterval.lower)
  have hxLower0 : 0 ≤ xLower := by
    norm_num [xLower, highLogTwoInterval]
  have hxLower1 : xLower < 1 := by
    norm_num [xLower, highLogTwoInterval]
  have hxUpper0 : 0 ≤ xUpper := by
    norm_num [xUpper, highLogTwoInterval]
  have hxUpper1 : xUpper < 1 := by
    norm_num [xUpper, highLogTwoInterval]
  have hlo := (logRatioInterval_contains hxLower0 hxLower1).1
  have hup := (logRatioInterval_contains hxUpper0 hxUpper1).2
  have hLlo : (0 : ℝ) < (highLogTwoInterval.lower : ℚ) := by
    norm_num [highLogTwoInterval]
  have hLhi : (0 : ℝ) < (highLogTwoInterval.upper : ℚ) := by
    norm_num [highLogTwoInterval]
  have hratioLower : ((((1 + xLower) / (1 - xLower) : ℚ) : ℝ)) =
      ((highLogTwoInterval.upper : ℚ) : ℝ)⁻¹ := by
    norm_num [xLower, highLogTwoInterval]
  have hratioUpper : ((((1 + xUpper) / (1 - xUpper) : ℚ) : ℝ)) =
      ((highLogTwoInterval.lower : ℚ) : ℝ)⁻¹ := by
    norm_num [xUpper, highLogTwoInterval]
  have hlogLower : Real.log
        ((((1 + xLower) / (1 - xLower) : ℚ) : ℝ)) =
      -Real.log ((highLogTwoInterval.upper : ℚ) : ℝ) := by
    rw [hratioLower, Real.log_inv]
  have hlogUpper : Real.log
        ((((1 + xUpper) / (1 - xUpper) : ℚ) : ℝ)) =
      -Real.log ((highLogTwoInterval.lower : ℚ) : ℝ) := by
    rw [hratioUpper, Real.log_inv]
  have hmonoLower :
      -Real.log ((highLogTwoInterval.upper : ℚ) : ℝ) ≤
        -Real.log yoshidaLength := by
    have := Real.log_le_log yoshidaLength_pos highLogTwoInterval_contains.2
    linarith
  have hmonoUpper : -Real.log yoshidaLength ≤
      -Real.log ((highLogTwoInterval.lower : ℚ) : ℝ) := by
    have := Real.log_le_log hLlo highLogTwoInterval_contains.1
    linarith
  unfold negLogLengthInterval
  dsimp only
  exact ⟨by rw [← hlogLower] at hmonoLower; exact hlo.trans hmonoLower,
    by rw [← hlogUpper] at hmonoUpper; exact hmonoUpper.trans hup⟩

private def highYInterval (n : ℕ) : RatInterval :=
  ⟨piFineInterval.lower * n / highLogTwoInterval.upper,
    piFineInterval.upper * n / highLogTwoInterval.lower⟩

private theorem highYInterval_contains (n : ℕ) :
    (highYInterval n).Contains
      (YoshidaDiagonalUniformIdentity.yoshidaY n) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnum0 : 0 ≤ Real.pi * (n : ℝ) :=
    mul_nonneg Real.pi_pos.le hn0
  have hnumLo : (piFineInterval.lower : ℝ) * (n : ℝ) ≤
      Real.pi * (n : ℝ) :=
    mul_le_mul_of_nonneg_right piFineInterval_contains.1 hn0
  have hnumHi : Real.pi * (n : ℝ) ≤
      (piFineInterval.upper : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right piFineInterval_contains.2 hn0
  have hLlo : (0 : ℝ) < (highLogTwoInterval.lower : ℚ) := by
    norm_num [highLogTwoInterval]
  have hLup : yoshidaLength ≤
      (highLogTwoInterval.upper : ℚ) := highLogTwoInterval_contains.2
  have hLloLe : (highLogTwoInterval.lower : ℚ) ≤
      yoshidaLength := highLogTwoInterval_contains.1
  have hyEq : YoshidaDiagonalUniformIdentity.yoshidaY n =
      Real.pi * (n : ℝ) / yoshidaLength := by
    unfold YoshidaDiagonalUniformIdentity.yoshidaY yoshidaKappa
    ring
  rw [hyEq]
  unfold highYInterval
  constructor
  · norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    exact div_le_div₀ hnum0 hnumLo yoshidaLength_pos hLup
  · norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    exact div_le_div₀
      (mul_nonneg (by norm_num [piFineInterval]) hn0)
      hnumHi hLlo hLloLe

private theorem highYInterval_lower_pos
    {n : ℕ} (hn : n ≠ 0) :
    0 < (highYInterval n).lower := by
  unfold highYInterval piFineInterval highLogTwoInterval
  positivity

private def highPositiveSquare (I : RatInterval) : RatInterval :=
  ⟨I.lower ^ 2, I.upper ^ 2⟩

private theorem highPositiveSquare_contains
    {I : RatInterval} {x : ℝ} (hI0 : 0 ≤ I.lower)
    (hx : I.Contains x) :
    (highPositiveSquare I).Contains (x ^ 2) := by
  unfold Contains at hx
  unfold highPositiveSquare Contains
  norm_num only [Rat.cast_pow]
  constructor
  · exact pow_le_pow_left₀ (by exact_mod_cast hI0) hx.1 2
  · exact pow_le_pow_left₀ (by
      exact (show (0 : ℝ) ≤ (I.lower : ℚ) by exact_mod_cast hI0).trans hx.1)
      hx.2 2

private def highSmallZInterval (n : ℕ) : RatInterval :=
  ⟨highLogTwoInterval.lower ^ 2 /
      (16 * piFineInterval.upper ^ 2 * (n : ℚ) ^ 2),
    highLogTwoInterval.upper ^ 2 /
      (16 * piFineInterval.lower ^ 2 * (n : ℚ) ^ 2)⟩

private theorem highSmallZInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highSmallZInterval n).Contains
      (yoshidaLength ^ 2 /
        (16 * Real.pi ^ 2 * (n : ℝ) ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hLlo : (0 : ℝ) ≤ (highLogTwoInterval.lower : ℚ) := by
    norm_num [highLogTwoInterval]
  have hLsqLo : ((highLogTwoInterval.lower : ℚ) : ℝ) ^ 2 ≤
      yoshidaLength ^ 2 :=
    pow_le_pow_left₀ hLlo highLogTwoInterval_contains.1 2
  have hLsqHi : yoshidaLength ^ 2 ≤
      ((highLogTwoInterval.upper : ℚ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ yoshidaLength_pos.le
      highLogTwoInterval_contains.2 2
  have hpiLo : (0 : ℝ) ≤ (piFineInterval.lower : ℚ) := by
    norm_num [piFineInterval]
  have hpiSqLo : ((piFineInterval.lower : ℚ) : ℝ) ^ 2 ≤
      Real.pi ^ 2 := pow_le_pow_left₀ hpiLo piFineInterval_contains.1 2
  have hpiSqHi : Real.pi ^ 2 ≤
      ((piFineInterval.upper : ℚ) : ℝ) ^ 2 :=
    pow_le_pow_left₀ Real.pi_pos.le piFineInterval_contains.2 2
  have hdenLo : 0 < 16 * ((piFineInterval.lower : ℚ) : ℝ) ^ 2 *
      (n : ℝ) ^ 2 := by
    exact mul_pos (mul_pos (by norm_num)
      (sq_pos_of_pos (by norm_num [piFineInterval]))) (sq_pos_of_pos hnR)
  have hden : 0 < 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
      (sq_pos_of_pos hnR)
  have hdenHi : 16 * Real.pi ^ 2 * (n : ℝ) ^ 2 ≤
      16 * ((piFineInterval.upper : ℚ) : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
    gcongr
  have hdenLoLe :
      16 * ((piFineInterval.lower : ℚ) : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤
        16 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by
    gcongr
  unfold highSmallZInterval Contains
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat]
  exact ⟨div_le_div₀ (sq_nonneg _) hLsqLo hden hdenHi,
    div_le_div₀ (sq_nonneg _) hLsqHi hdenLo hdenLoLe⟩

private def highLogOnePlusInterval (I : RatInterval) : RatInterval :=
  ⟨2 * I.lower / (I.lower + 2), I.upper⟩

private theorem highLogOnePlusInterval_contains
    {I : RatInterval} {z : ℝ} (hI0 : 0 ≤ I.lower)
    (hz : I.Contains z) :
    (highLogOnePlusInterval I).Contains (Real.log (1 + z)) := by
  have hloR : (0 : ℝ) ≤ (I.lower : ℚ) := by exact_mod_cast hI0
  have hz0 : 0 ≤ z := hloR.trans hz.1
  have hdenLo : 0 < (I.lower : ℝ) + 2 := by linarith
  have hdenZ : 0 < z + 2 := by linarith
  have hmono :
      2 * (I.lower : ℝ) / ((I.lower : ℝ) + 2) ≤
        2 * z / (z + 2) := by
    rw [div_le_div_iff₀ hdenLo hdenZ]
    nlinarith [hz.1]
  have hlower := Real.le_log_one_add_of_nonneg hz0
  have hupper := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + z)
  unfold highLogOnePlusInterval Contains
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat]
  exact ⟨hmono.trans hlower, by linarith [hupper, hz.2]⟩

private def highDiagonalLogCoreInterval (n : ℕ) : RatInterval :=
  highLogNatInterval n + negLogLengthInterval +
    highLogOnePlusInterval (highSmallZInterval n) / pure 2

private theorem diagonal_log_core_eq
    {n : ℕ} (hn : n ≠ 0) :
    Real.log ((1 / 16 : ℝ) +
        YoshidaDiagonalUniformIdentity.yoshidaY n ^ 2) / 2 -
        Real.log Real.pi =
      Real.log (n : ℝ) - Real.log yoshidaLength +
        Real.log (1 + yoshidaLength ^ 2 /
          (16 * Real.pi ^ 2 * (n : ℝ) ^ 2)) / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hL0 := yoshidaLength_pos.ne'
  have hpi0 := Real.pi_pos.ne'
  let z : ℝ := yoshidaLength ^ 2 /
    (16 * Real.pi ^ 2 * (n : ℝ) ^ 2)
  have hz0 : 0 ≤ z := by dsimp only [z]; positivity
  have hfactor : (1 / 16 : ℝ) +
      YoshidaDiagonalUniformIdentity.yoshidaY n ^ 2 =
      (Real.pi * (n : ℝ) / yoshidaLength) ^ 2 * (1 + z) := by
    unfold YoshidaDiagonalUniformIdentity.yoshidaY yoshidaKappa
    dsimp only [z]
    field_simp [hL0, hpi0, ne_of_gt hnR]
    ring
  rw [hfactor, Real.log_mul (by positivity) (by linarith),
    Real.log_pow, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  dsimp only [z]
  ring

private theorem highDiagonalLogCoreInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highDiagonalLogCoreInterval n).Contains
      (Real.log ((1 / 16 : ℝ) +
          YoshidaDiagonalUniformIdentity.yoshidaY n ^ 2) / 2 -
        Real.log Real.pi) := by
  rw [diagonal_log_core_eq hn]
  have hlogn := highLogNatInterval_contains hn
  have hlogL := negLogLengthInterval_contains
  have hz := highSmallZInterval_contains hn
  have hz0 : 0 ≤ (highSmallZInterval n).lower := by
    unfold highSmallZInterval highLogTwoInterval piFineInterval
    positivity
  have hlogz := highLogOnePlusInterval_contains hz0 hz
  have htwo : (RatInterval.pure 2).Contains (2 : ℝ) := contains_pure 2
  unfold highDiagonalLogCoreInterval
  exact contains_add (contains_add hlogn hlogL)
    (contains_div_of_pos (by norm_num [RatInterval.pure]) hlogz htwo)

private def highYSqInterval (n : ℕ) : RatInterval :=
  highPositiveSquare (highYInterval n)

private theorem highYSqInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highYSqInterval n).Contains
      (YoshidaDiagonalUniformIdentity.yoshidaY n ^ 2) := by
  exact highPositiveSquare_contains (highYInterval_lower_pos hn).le
    (highYInterval_contains n)

private def highPositivePow (I : RatInterval) (k : ℕ) : RatInterval :=
  ⟨I.lower ^ k, I.upper ^ k⟩

private theorem highPositivePow_contains
    {I : RatInterval} {x : ℝ} (hI0 : 0 ≤ I.lower)
    (hx : I.Contains x) (k : ℕ) :
    (highPositivePow I k).Contains (x ^ k) := by
  unfold Contains at hx
  unfold highPositivePow Contains
  norm_num only [Rat.cast_pow]
  constructor
  · exact pow_le_pow_left₀ (by exact_mod_cast hI0) hx.1 k
  · exact pow_le_pow_left₀ (by
      exact (show (0 : ℝ) ≤ (I.lower : ℚ) by exact_mod_cast hI0).trans hx.1)
      hx.2 k

private def highProfileDenInterval (n : ℕ) (u : ℚ) : RatInterval :=
  pure (u ^ 2) + highYSqInterval n

private theorem highProfileDenInterval_contains
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    (highProfileDenInterval n u).Contains
      ((u : ℝ) ^ 2 + YoshidaDiagonalUniformIdentity.yoshidaY n ^ 2) := by
  have huSq : (pure (u ^ 2)).Contains ((u : ℝ) ^ 2) := by
    norm_num [Contains, RatInterval.pure]
  exact contains_add huSq (highYSqInterval_contains hn)

private theorem highProfileDenInterval_lower_pos
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    0 < (highProfileDenInterval n u).lower := by
  unfold highProfileDenInterval highYSqInterval highPositiveSquare
    highYInterval
  change 0 < u ^ 2 +
    (piFineInterval.lower * n / highLogTwoInterval.upper) ^ 2
  have hyn : 0 < piFineInterval.lower * n / highLogTwoInterval.upper := by
    unfold piFineInterval highLogTwoInterval
    positivity
  nlinarith [sq_pos_of_pos hyn, sq_nonneg u]

private def highProfileInterval (n : ℕ) (u : ℚ) : RatInterval :=
  pure u / highProfileDenInterval n u

private theorem highProfileInterval_contains
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    (highProfileInterval n u).Contains
      (reciprocalRealPart
        (YoshidaDiagonalUniformIdentity.yoshidaY n) (u : ℝ)) := by
  unfold highProfileInterval reciprocalRealPart
  exact contains_div_of_pos (highProfileDenInterval_lower_pos hn u)
    (contains_pure u) (highProfileDenInterval_contains hn u)

private def highProfileDerivInterval (n : ℕ) (u : ℚ) : RatInterval :=
  (highYSqInterval n - pure (u ^ 2)) /
    highPositivePow (highProfileDenInterval n u) 2

private theorem highProfileDerivInterval_contains
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    (highProfileDerivInterval n u).Contains
      (reciprocalRealPartDeriv
        (YoshidaDiagonalUniformIdentity.yoshidaY n) (u : ℝ)) := by
  have hden := highProfileDenInterval_contains hn u
  have hdenPow := highPositivePow_contains
    (highProfileDenInterval_lower_pos hn u).le hden 2
  have huSq : (pure (u ^ 2)).Contains ((u : ℝ) ^ 2) := by
    norm_num [Contains, RatInterval.pure]
  have hnum := contains_sub (highYSqInterval_contains hn)
    huSq
  unfold highProfileDerivInterval reciprocalRealPartDeriv
  exact contains_div_of_pos (by
    unfold highPositivePow
    exact pow_pos (highProfileDenInterval_lower_pos hn u) 2)
    hnum hdenPow

private def highProfileSecondInterval (n : ℕ) (u : ℚ) : RatInterval :=
  (pure (2 * u) *
      (pure (u ^ 2) - pure 3 * highYSqInterval n)) /
    highPositivePow (highProfileDenInterval n u) 3

private theorem highProfileSecondInterval_contains
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    (highProfileSecondInterval n u).Contains
      (reciprocalRealPartSecondDeriv
        (YoshidaDiagonalUniformIdentity.yoshidaY n) (u : ℝ)) := by
  have hden := highProfileDenInterval_contains hn u
  have hdenPow := highPositivePow_contains
    (highProfileDenInterval_lower_pos hn u).le hden 3
  have huSq : (pure (u ^ 2)).Contains ((u : ℝ) ^ 2) := by
    norm_num [Contains, RatInterval.pure]
  have hnum := contains_mul (contains_pure (2 * u))
    (contains_sub huSq
      (contains_mul (contains_pure 3) (highYSqInterval_contains hn)))
  unfold highProfileSecondInterval reciprocalRealPartSecondDeriv
  exact contains_div_of_pos (by
    unfold highPositivePow
    exact pow_pos (highProfileDenInterval_lower_pos hn u) 3)
    (by
      convert hnum using 1
      all_goals norm_num) hdenPow

private def highProfileThirdInterval (n : ℕ) (u : ℚ) : RatInterval :=
  (pure (-6) *
      (pure (u ^ 4) - pure (6 * u ^ 2) * highYSqInterval n +
        highPositiveSquare (highYSqInterval n))) /
    highPositivePow (highProfileDenInterval n u) 4

private theorem highProfileThirdInterval_contains
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    (highProfileThirdInterval n u).Contains
      (diagonalHighProfileThirdDeriv
        (YoshidaDiagonalUniformIdentity.yoshidaY n) ((u : ℝ) - 1 / 4)) := by
  have hp := highYSqInterval_contains hn
  have hp0 : 0 ≤ (highYSqInterval n).lower := by
    unfold highYSqInterval highPositiveSquare
    positivity
  have hp2 := highPositiveSquare_contains hp0 hp
  have huFourth : (pure (u ^ 4)).Contains ((u : ℝ) ^ 4) := by
    norm_num [Contains, RatInterval.pure]
  have hpoly := contains_add
    (contains_sub huFourth
      (contains_mul (contains_pure (6 * u ^ 2)) hp)) hp2
  have hnum := contains_mul (contains_pure (-6)) hpoly
  have hden := highProfileDenInterval_contains hn u
  have hdenPow := highPositivePow_contains
    (highProfileDenInterval_lower_pos hn u).le hden 4
  unfold highProfileThirdInterval diagonalHighProfileThirdDeriv
  dsimp only
  have hquot := contains_div_of_pos (by
    unfold highPositivePow
    exact pow_pos (highProfileDenInterval_lower_pos hn u) 4)
    hnum hdenPow
  convert hquot using 1
  all_goals norm_num
  all_goals ring

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

private def highKappaSqInterval (n : ℕ) : RatInterval :=
  pure 4 * highYSqInterval n

private theorem highKappaSqInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highKappaSqInterval n).Contains (yoshidaKappa n ^ 2) := by
  have h := contains_mul (contains_pure 4) (highYSqInterval_contains hn)
  have hk : yoshidaKappa n =
      2 * YoshidaDiagonalUniformIdentity.yoshidaY n := by
    unfold YoshidaDiagonalUniformIdentity.yoshidaY
    ring
  rw [hk]
  convert h using 1
  ring

private theorem highKappaSqInterval_lower_nonneg (n : ℕ) :
    0 ≤ (highKappaSqInterval n).lower := by
  unfold highKappaSqInterval highYSqInterval highPositiveSquare
    highYInterval
  change 0 ≤ min
    (min (4 * (piFineInterval.lower * n / highLogTwoInterval.upper) ^ 2)
      (4 * (piFineInterval.upper * n / highLogTwoInterval.lower) ^ 2))
    (min (4 * (piFineInterval.lower * n / highLogTwoInterval.upper) ^ 2)
      (4 * (piFineInterval.upper * n / highLogTwoInterval.lower) ^ 2))
  simp only [min_self, le_min_iff]
  constructor <;> positivity

private def highRampInterval (n : ℕ) : RatInterval :=
  let L := highLogTwoInterval
  let p := highKappaSqInterval n
  let a := pure (-1 / 2 : ℚ)
  let aSq := pure (1 / 4 : ℚ)
  ((sqrtTwoInterval - pure 1 + a * L) * (aSq - p) +
      pure 2 * a * p * L) /
    (L * highPositiveSquare (aSq + p))

private theorem highRampInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highRampInterval n).Contains
      (diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
        (-1 / 2) (Real.sqrt 2)) := by
  let L := highLogTwoInterval
  let p := highKappaSqInterval n
  let a := pure (-1 / 2 : ℚ)
  let aSq := pure (1 / 4 : ℚ)
  have hL : L.Contains yoshidaLength := highLogTwoInterval_contains
  have hp : p.Contains (yoshidaKappa n ^ 2) :=
    highKappaSqInterval_contains hn
  have ha : a.Contains (-1 / 2 : ℝ) := by
    norm_num [a, Contains, RatInterval.pure]
  have haSq : aSq.Contains ((-1 / 2 : ℝ) ^ 2) := by
    norm_num [aSq, Contains, RatInterval.pure]
  have hsqrt := sqrtTwoInterval_contains
  have hsum := contains_add haSq hp
  have hsumLower : 0 < (aSq + p).lower := by
    change 0 < (1 / 4 : ℚ) + p.lower
    have hp0 : 0 ≤ p.lower := by
      simpa only [p] using highKappaSqInterval_lower_nonneg n
    linarith
  have hsq := highPositiveSquare_contains hsumLower.le hsum
  have hden := contains_mul hL hsq
  have hdenLower : 0 < (L * highPositiveSquare (aSq + p)).lower := by
    apply mul_lower_pos_of_pos
    · norm_num [L, highLogTwoInterval]
    · unfold highPositiveSquare
      exact sq_pos_of_pos hsumLower
    · exact valid_of_contains hL
    · exact valid_of_contains hsq
  have hnum := contains_add
    (contains_mul
      (contains_add (contains_sub hsqrt (contains_pure 1))
        (contains_mul ha hL))
      (contains_sub haSq hp))
    (contains_mul (contains_mul (contains_mul (contains_pure 2) ha) hp) hL)
  unfold highRampInterval diagonalRampClosed
  dsimp only
  exact contains_div_of_pos hdenLower (by
    convert hnum using 1
    all_goals ring) hden

private def highDerivativeMainInterval (n : ℕ) : RatInterval :=
  -highProfileInterval n (5 / 4) +
      highProfileDerivInterval n (5 / 4) / pure 2 -
    highProfileSecondInterval n (5 / 4) / pure 12

private theorem highDerivativeMainInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highDerivativeMainInterval n).Contains
      (diagonalDerivativeTsumMain
        (YoshidaDiagonalUniformIdentity.yoshidaY n)) := by
  have hp := highProfileInterval_contains hn (5 / 4)
  have hd := highProfileDerivInterval_contains hn (5 / 4)
  have hs := highProfileSecondInterval_contains hn (5 / 4)
  have htwo : (pure 2).Contains (2 : ℝ) := contains_pure 2
  have htwelve : (pure 12).Contains (12 : ℝ) := contains_pure 12
  have hcombine := contains_sub
    (contains_add (contains_neg hp)
      (contains_div_of_pos (by norm_num [RatInterval.pure]) hd htwo))
    (contains_div_of_pos (by norm_num [RatInterval.pure]) hs htwelve)
  unfold highDerivativeMainInterval diagonalDerivativeTsumMain
    diagonalHighProfile diagonalHighProfileDeriv
    diagonalHighProfileSecondDeriv
  dsimp only
  convert hcombine using 1
  all_goals norm_num
  all_goals unfold reciprocalRealPartSecondDeriv
  all_goals ring

private def highNegQMainInterval (n : ℕ) : RatInterval :=
  pure 2 /
    (pure 3 * sqrtTwoInterval * highLogTwoInterval *
      highKappaSqInterval n)

private theorem highNegQMainInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highNegQMainInterval n).Contains (-diagonalQMain n) := by
  let D := pure 3 * sqrtTwoInterval * highLogTwoInterval *
    highKappaSqInterval n
  have h3 : (pure 3).Contains (3 : ℝ) := contains_pure 3
  have hs := sqrtTwoInterval_contains
  have hL := highLogTwoInterval_contains
  have hp := highKappaSqInterval_contains hn
  have hden : D.Contains
      (3 * Real.sqrt 2 * yoshidaLength * yoshidaKappa n ^ 2) := by
    dsimp only [D]
    exact contains_mul (contains_mul (contains_mul h3 hs) hL) hp
  have hpLower : 0 < (highKappaSqInterval n).lower := by
    unfold highKappaSqInterval highYSqInterval highPositiveSquare
      highYInterval
    have hy : 0 < piFineInterval.lower * n / highLogTwoInterval.upper := by
      unfold piFineInterval highLogTwoInterval
      positivity
    have hyUpper : 0 <
        piFineInterval.upper * n / highLogTwoInterval.lower := by
      unfold piFineInterval highLogTwoInterval
      positivity
    change 0 < min
      (min (4 * (piFineInterval.lower * n /
          highLogTwoInterval.upper) ^ 2)
        (4 * (piFineInterval.upper * n /
          highLogTwoInterval.lower) ^ 2))
      (min (4 * (piFineInterval.lower * n /
          highLogTwoInterval.upper) ^ 2)
        (4 * (piFineInterval.upper * n /
          highLogTwoInterval.lower) ^ 2))
    simp only [min_self, lt_min_iff]
    exact ⟨mul_pos (by norm_num) (sq_pos_of_pos hy),
      mul_pos (by norm_num) (sq_pos_of_pos hyUpper)⟩
  have h3s : 0 < (RatInterval.pure 3 * sqrtTwoInterval).lower := by
    apply mul_lower_pos_of_pos
    · norm_num [RatInterval.pure]
    · norm_num [sqrtTwoInterval]
    · exact valid_of_contains h3
    · exact valid_of_contains hs
  have h3sL : 0 <
      (RatInterval.pure 3 * sqrtTwoInterval * highLogTwoInterval).lower := by
    apply mul_lower_pos_of_pos
    · exact h3s
    · norm_num [highLogTwoInterval]
    · exact valid_of_contains (contains_mul h3 hs)
    · exact valid_of_contains hL
  have hDLower : 0 < D.lower := by
    dsimp only [D]
    apply mul_lower_pos_of_pos h3sL hpLower
    · exact valid_of_contains (contains_mul (contains_mul h3 hs) hL)
    · exact valid_of_contains hp
  unfold highNegQMainInterval diagonalQMain
  have hquot := contains_div_of_pos hDLower (contains_pure 2) hden
  convert hquot using 1
  ring

private def highDiagonalUniformMain (n : ℕ) : ℝ :=
  diagonalDigammaMain
      (YoshidaDiagonalUniformIdentity.yoshidaY n) -
    Real.log Real.pi +
    2 * diagonalRampClosed yoshidaLength (yoshidaKappa n ^ 2)
      (-1 / 2) (Real.sqrt 2) +
    diagonalHighProfile
      (YoshidaDiagonalUniformIdentity.yoshidaY n) 0 -
    diagonalDerivativeTsumMain
        (YoshidaDiagonalUniformIdentity.yoshidaY n) /
      (2 * yoshidaLength) -
    diagonalQMain n

private def highDiagonalUniformMainInterval (n : ℕ) : RatInterval :=
  highDiagonalLogCoreInterval n +
      pure 2 * highRampInterval n +
      highProfileInterval n (1 / 4) / pure 2 +
      highProfileDerivInterval n (1 / 4) / pure 12 -
      highProfileThirdInterval n (1 / 4) / pure 720 -
      highDerivativeMainInterval n /
        (pure 2 * highLogTwoInterval) +
    highNegQMainInterval n

private theorem highDiagonalUniformMainInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highDiagonalUniformMainInterval n).Contains
      (highDiagonalUniformMain n) := by
  have hlog := highDiagonalLogCoreInterval_contains hn
  have hramp := highRampInterval_contains hn
  have hp0 := highProfileInterval_contains hn (1 / 4)
  have hd0 := highProfileDerivInterval_contains hn (1 / 4)
  have ht0 := highProfileThirdInterval_contains hn (1 / 4)
  have hderiv := highDerivativeMainInterval_contains hn
  have hq := highNegQMainInterval_contains hn
  have htwo : (pure 2).Contains (2 : ℝ) := contains_pure 2
  have htwelve : (pure 12).Contains (12 : ℝ) := contains_pure 12
  have hsevenTwenty : (pure 720).Contains (720 : ℝ) := contains_pure 720
  have htwoL := contains_mul htwo highLogTwoInterval_contains
  have htwoLpos : 0 < (pure 2 * highLogTwoInterval).lower := by
    apply mul_lower_pos_of_pos
    · norm_num [RatInterval.pure]
    · norm_num [highLogTwoInterval]
    · exact valid_of_contains htwo
    · exact valid_of_contains highLogTwoInterval_contains
  have hcombine := contains_add
    (contains_sub
      (contains_sub
        (contains_add
          (contains_add
            (contains_add hlog (contains_mul htwo hramp))
            (contains_div_of_pos (by norm_num [RatInterval.pure]) hp0 htwo))
          (contains_div_of_pos (by norm_num [RatInterval.pure]) hd0 htwelve))
        (contains_div_of_pos (by norm_num [RatInterval.pure]) ht0 hsevenTwenty))
      (contains_div_of_pos htwoLpos hderiv htwoL))
    hq
  unfold highDiagonalUniformMainInterval highDiagonalUniformMain
    diagonalDigammaMain diagonalHighProfile diagonalHighProfileDeriv
  convert hcombine using 1
  all_goals norm_num
  all_goals ring

private def highDigammaRadius (n : ℕ) : ℚ :=
  4 / (3 * (highYInterval n).lower ^ 5)

private def highDerivativeRadius (n : ℕ) : ℚ :=
  5 / (4 * highLogTwoInterval.lower *
    (highYInterval n).lower ^ 4)

private def highQRadius (n : ℕ) : ℚ :=
  425 / (18 * sqrtTwoInterval.lower * highLogTwoInterval.lower *
    (2 * (highYInterval n).lower) ^ 4)

private def highDiagonalUniformErrorInterval (n : ℕ) : RatInterval :=
  ⟨-(highDigammaRadius n + highDerivativeRadius n + highQRadius n),
    highDigammaRadius n + highDerivativeRadius n⟩

private theorem highDigammaRadius_bound
    {n : ℕ} (hn : n ≠ 0) :
    4 / (3 * YoshidaDiagonalUniformIdentity.yoshidaY n ^ 5) ≤
      (highDigammaRadius n : ℝ) := by
  have hy := highYInterval_contains n
  have hylQ := highYInterval_lower_pos hn
  have hyl : (0 : ℝ) < ((highYInterval n).lower : ℚ) := by
    exact_mod_cast hylQ
  have hden :
      3 * ((highYInterval n).lower : ℝ) ^ 5 ≤
        3 * YoshidaDiagonalUniformIdentity.yoshidaY n ^ 5 := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hyl.le hy.1 5) (by norm_num)
  unfold highDigammaRadius
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

private theorem highDerivativeRadius_bound
    {n : ℕ} (hn : n ≠ 0) :
    5 / (4 * yoshidaLength *
        YoshidaDiagonalUniformIdentity.yoshidaY n ^ 4) ≤
      (highDerivativeRadius n : ℝ) := by
  have hy := highYInterval_contains n
  have hylQ := highYInterval_lower_pos hn
  have hyl : (0 : ℝ) < ((highYInterval n).lower : ℚ) := by
    exact_mod_cast hylQ
  have hLlo : (0 : ℝ) < (highLogTwoInterval.lower : ℚ) := by
    norm_num [highLogTwoInterval]
  have hden :
      4 * (highLogTwoInterval.lower : ℝ) *
          (highYInterval n).lower ^ 4 ≤
        4 * yoshidaLength *
          YoshidaDiagonalUniformIdentity.yoshidaY n ^ 4 := by
    have hpow : ((highYInterval n).lower : ℝ) ^ 4 ≤
        YoshidaDiagonalUniformIdentity.yoshidaY n ^ 4 :=
      pow_le_pow_left₀ hyl.le hy.1 4
    calc
      4 * (highLogTwoInterval.lower : ℝ) *
          (highYInterval n).lower ^ 4 ≤
          4 * yoshidaLength * (highYInterval n).lower ^ 4 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left highLogTwoInterval_contains.1
            (by norm_num)) (pow_nonneg hyl.le 4)
      _ ≤ 4 * yoshidaLength *
          YoshidaDiagonalUniformIdentity.yoshidaY n ^ 4 :=
        mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (by norm_num) yoshidaLength_pos.le)
  unfold highDerivativeRadius
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

private theorem highQRadius_bound
    {n : ℕ} (hn : n ≠ 0) :
    425 / (18 * Real.sqrt 2 * yoshidaLength *
        (yoshidaKappa n ^ 2) ^ 2) ≤
      (highQRadius n : ℝ) := by
  have hy := highYInterval_contains n
  have hylQ := highYInterval_lower_pos hn
  have hyl : (0 : ℝ) < ((highYInterval n).lower : ℚ) := by
    exact_mod_cast hylQ
  have hslo : (0 : ℝ) < (sqrtTwoInterval.lower : ℚ) := by
    norm_num [sqrtTwoInterval]
  have hLlo : (0 : ℝ) < (highLogTwoInterval.lower : ℚ) := by
    norm_num [highLogTwoInterval]
  have hk : yoshidaKappa n =
      2 * YoshidaDiagonalUniformIdentity.yoshidaY n := by
    unfold YoshidaDiagonalUniformIdentity.yoshidaY
    ring
  have hden :
      18 * (sqrtTwoInterval.lower : ℝ) *
          (highLogTwoInterval.lower : ℝ) *
          (2 * (highYInterval n).lower) ^ 4 ≤
        18 * Real.sqrt 2 * yoshidaLength *
          (yoshidaKappa n ^ 2) ^ 2 := by
    rw [hk]
    have hpow : (2 * (highYInterval n).lower : ℝ) ^ 4 ≤
        (2 * YoshidaDiagonalUniformIdentity.yoshidaY n) ^ 4 := by
      exact pow_le_pow_left₀ (mul_nonneg (by norm_num) hyl.le)
        (mul_le_mul_of_nonneg_left hy.1 (by norm_num)) 4
    have hfirst :
        18 * (sqrtTwoInterval.lower : ℝ) *
            (highLogTwoInterval.lower : ℝ) ≤
          18 * Real.sqrt 2 * yoshidaLength := by
      calc
        18 * (sqrtTwoInterval.lower : ℝ) *
            (highLogTwoInterval.lower : ℝ) ≤
            18 * Real.sqrt 2 * (highLogTwoInterval.lower : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left sqrtTwoInterval_contains.1
              (by norm_num)) hLlo.le
        _ ≤ 18 * Real.sqrt 2 * yoshidaLength :=
          mul_le_mul_of_nonneg_left highLogTwoInterval_contains.1
            (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2))
    convert mul_le_mul hfirst hpow
      (pow_nonneg (mul_nonneg (by norm_num) hyl.le) 4)
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18)
        (Real.sqrt_nonneg 2)) yoshidaLength_pos.le) using 1
    all_goals ring
  unfold highQRadius
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

private theorem highDiagonalUniformErrorInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highDiagonalUniformErrorInterval n).Contains
      (yoshidaDiagonalMoment n - highDiagonalUniformMain n) := by
  let y := YoshidaDiagonalUniformIdentity.yoshidaY n
  let eD :=
    (Complex.digamma ((1 / 4 : ℝ) + y * Complex.I)).re -
      diagonalDigammaMain y
  let eR :=
    (∑' j : ℕ, diagonalHighDerivativeTerm n j) /
        (2 * yoshidaLength) -
      diagonalDerivativeTsumMain y / (2 * yoshidaLength)
  let eQ := (-diagonalHighQ n) - (-diagonalQMain n)
  have hy : 0 < y := by
    dsimp only [y]
    exact (show (0 : ℝ) < (highYInterval n).lower by
      exact_mod_cast highYInterval_lower_pos hn).trans_le
        (highYInterval_contains n).1
  have hd0 := digamma_quarter_vertical_re_sub_highMain_abs_le hy
  have hdRadius := highDigammaRadius_bound hn
  have hd : |eD| ≤ (highDigammaRadius n : ℝ) := by
    exact hd0.trans hdRadius
  have hr0 := diagonalHighDerivativeTerm_normalized_sub_main_abs_le hn
  have hrRadius := highDerivativeRadius_bound hn
  have hr : |eR| ≤ (highDerivativeRadius n : ℝ) := by
    exact hr0.trans hrRadius
  have hq0 := neg_diagonalHighQ_sub_neg_main_bounds
    (Nat.one_le_iff_ne_zero.mpr hn)
  have hqRadius := highQRadius_bound hn
  have hqLower : -(highQRadius n : ℝ) ≤ eQ := by
    exact (neg_le_neg hqRadius).trans hq0.1
  have hqUpper : eQ ≤ 0 := hq0.2
  have hidentity :
      yoshidaDiagonalMoment n - highDiagonalUniformMain n =
        eD - eR + eQ := by
    rw [yoshidaDiagonalMoment_eq_uniformSeries hn]
    dsimp only [eD, eR, eQ, y]
    unfold highDiagonalUniformMain
    ring
  rw [hidentity]
  rw [abs_le] at hd hr
  unfold highDiagonalUniformErrorInterval Contains
  norm_num only [Rat.cast_neg, Rat.cast_add]
  constructor <;> linarith [hd.1, hd.2, hr.1, hr.2]

/-! ## Structural width estimates -/

private structure HighIntervalMetrics (I : RatInterval) (B W : ℚ) : Prop where
  valid : I.Valid
  absBound : I.AbsBound B
  width_le : width I ≤ W
  bound_nonneg : 0 ≤ B
  width_nonneg : 0 ≤ W

private theorem highMetrics_pure {q B : ℚ} (hq : |q| ≤ B) (hB : 0 ≤ B) :
    HighIntervalMetrics (pure q) B 0 := by
  exact ⟨valid_pure q, absBound_pure hq, by rw [width_pure], hB, le_rfl⟩

private theorem HighIntervalMetrics.weaken
    {I : RatInterval} {B W B' W' : ℚ}
    (h : HighIntervalMetrics I B W) (hB : B ≤ B') (hW : W ≤ W') :
    HighIntervalMetrics I B' W' := by
  refine ⟨h.valid, ?_, h.width_le.trans hW,
    h.bound_nonneg.trans hB, h.width_nonneg.trans hW⟩
  rcases h.absBound with ⟨hl, hu⟩
  exact ⟨by linarith, hu.trans hB⟩

private theorem highMetrics_add
    {I J : RatInterval} {BI BJ WI WJ : ℚ}
    (hI : HighIntervalMetrics I BI WI)
    (hJ : HighIntervalMetrics J BJ WJ) :
    HighIntervalMetrics (I + J) (BI + BJ) (WI + WJ) := by
  refine ⟨valid_add hI.valid hJ.valid,
    absBound_add hI.absBound hJ.absBound, ?_,
    add_nonneg hI.bound_nonneg hJ.bound_nonneg,
    add_nonneg hI.width_nonneg hJ.width_nonneg⟩
  rw [width_add]
  exact add_le_add hI.width_le hJ.width_le

private theorem highMetrics_sub
    {I J : RatInterval} {BI BJ WI WJ : ℚ}
    (hI : HighIntervalMetrics I BI WI)
    (hJ : HighIntervalMetrics J BJ WJ) :
    HighIntervalMetrics (I - J) (BI + BJ) (WI + WJ) := by
  refine ⟨valid_sub hI.valid hJ.valid,
    absBound_sub hI.absBound hJ.absBound, ?_,
    add_nonneg hI.bound_nonneg hJ.bound_nonneg,
    add_nonneg hI.width_nonneg hJ.width_nonneg⟩
  rw [width_sub]
  exact add_le_add hI.width_le hJ.width_le

private theorem highMetrics_neg
    {I : RatInterval} {B W : ℚ} (hI : HighIntervalMetrics I B W) :
    HighIntervalMetrics (-I) B W := by
  refine ⟨?_, ?_, ?_, hI.bound_nonneg, hI.width_nonneg⟩
  · change -I.upper ≤ -I.lower
    exact neg_le_neg hI.valid
  · exact ⟨by change -B ≤ -I.upper; linarith [hI.absBound.2],
      by change -I.lower ≤ B; linarith [hI.absBound.1]⟩
  · change (-I.lower) - (-I.upper) ≤ W
    have hw := hI.width_le
    unfold width at hw
    linarith [hw]

private theorem highMetrics_mul
    {I J : RatInterval} {BI BJ WI WJ : ℚ}
    (hI : HighIntervalMetrics I BI WI)
    (hJ : HighIntervalMetrics J BJ WJ) :
    HighIntervalMetrics (I * J) (BI * BJ) (BJ * WI + BI * WJ) := by
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

private theorem highMetrics_inv
    {I : RatInterval} {B W m : ℚ}
    (hI : HighIntervalMetrics I B W) (hm : 0 < m) (hml : m ≤ I.lower) :
    HighIntervalMetrics I⁻¹ m⁻¹ (W / m ^ 2) := by
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

private theorem highMetrics_div
    {I J : RatInterval} {BI BJ WI WJ m : ℚ}
    (hI : HighIntervalMetrics I BI WI)
    (hJ : HighIntervalMetrics J BJ WJ)
    (hm : 0 < m) (hml : m ≤ J.lower) :
    HighIntervalMetrics (I / J) (BI * m⁻¹)
      (m⁻¹ * WI + BI * (WJ / m ^ 2)) := by
  exact highMetrics_mul hI (highMetrics_inv hJ hm hml)

private theorem highMetrics_positiveSquare
    {I : RatInterval} {B W : ℚ}
    (hI : HighIntervalMetrics I B W) (hI0 : 0 ≤ I.lower) :
    HighIntervalMetrics (highPositiveSquare I) (B ^ 2) (2 * B * W) := by
  have hIu0 : 0 ≤ I.upper := hI0.trans hI.valid
  have hlB : I.lower ≤ B := hI.valid.trans hI.absBound.2
  have huB : I.upper ≤ B := hI.absBound.2
  refine ⟨?_, ?_, ?_, sq_nonneg B,
    mul_nonneg (mul_nonneg (by norm_num) hI.bound_nonneg)
      hI.width_nonneg⟩
  · unfold highPositiveSquare RatInterval.Valid
    nlinarith [mul_nonneg (sub_nonneg.mpr hI.valid)
      (add_nonneg hIu0 hI0)]
  · unfold highPositiveSquare AbsBound
    constructor <;> nlinarith [sq_nonneg I.lower, sq_nonneg I.upper]
  · unfold highPositiveSquare width
    have hfactor : I.upper ^ 2 - I.lower ^ 2 =
        (I.upper - I.lower) * (I.upper + I.lower) := by ring
    rw [hfactor]
    have hsum : I.upper + I.lower ≤ 2 * B := by linarith
    have hdiff : I.upper - I.lower ≤ W := hI.width_le
    nlinarith [mul_nonneg (sub_nonneg.mpr hI.valid)
      (add_nonneg hIu0 hI0),
      mul_le_mul hdiff hsum (add_nonneg hIu0 hI0)
        hI.width_nonneg]

private theorem logRatioInterval_width_eq (x : ℚ) :
    width (logRatioInterval x) = 2 * x ^ 37 / (1 - x ^ 2) := by
  unfold logRatioInterval logRatioUpper width
  dsimp only
  ring

set_option maxHeartbeats 2000000 in
private theorem logRatioInterval_structural_width_le
    {x : ℚ} (hx0 : 0 ≤ x) (hx : x ≤ 17 / 47) :
    width (logRatioInterval x) ≤ (1 / 1000000000000000 : ℚ) := by
  have hx1 : x < 1 := hx.trans_lt (by norm_num)
  have hpow : x ^ 37 ≤ (17 / 47 : ℚ) ^ 37 :=
    pow_le_pow_left₀ hx0 hx 37
  have hsq : x ^ 2 ≤ (17 / 47 : ℚ) ^ 2 :=
    pow_le_pow_left₀ hx0 hx 2
  have hden : (1 - (17 / 47 : ℚ) ^ 2) ≤ 1 - x ^ 2 := by
    linarith
  rw [logRatioInterval_width_eq]
  calc
    2 * x ^ 37 / (1 - x ^ 2) ≤
        2 * (17 / 47 : ℚ) ^ 37 / (1 - (17 / 47 : ℚ) ^ 2) :=
      div_le_div₀ (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 37))
        (mul_le_mul_of_nonneg_left hpow (by norm_num)) (by norm_num) hden
    _ ≤ (1 / 1000000000000000 : ℚ) := by norm_num

private theorem highLogNatRatioInterval_valid_and_width
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200) :
    (highLogNatRatioInterval n).Valid ∧
      width (highLogNatRatioInterval n) ≤
        (1 / 1000000000000000 : ℚ) := by
  unfold highLogNatRatioInterval
  split_ifs with hn128
  · let x : ℚ := ((128 - n : ℕ) : ℚ) / ((128 + n : ℕ) : ℚ)
    have hx0 : 0 ≤ x := by dsimp only [x]; positivity
    have hx : x ≤ 17 / 47 := by
      dsimp only [x]
      rw [div_le_iff₀ (by positivity)]
      norm_num only [Nat.cast_sub hn128, Nat.cast_add, Nat.cast_ofNat]
      have hnq : (60 : ℚ) ≤ n := by exact_mod_cast hn60
      linarith
    have hx1 : x < 1 := hx.trans_lt (by norm_num)
    have hc := logRatioInterval_contains hx0 hx1
    constructor
    · change (-logRatioInterval x).Valid
      change -(logRatioInterval x).upper ≤ -(logRatioInterval x).lower
      exact neg_le_neg (valid_of_contains hc)
    · change width (-logRatioInterval x) ≤ _
      change -(logRatioInterval x).lower - -(logRatioInterval x).upper ≤ _
      have hw := logRatioInterval_structural_width_le hx0 hx
      unfold width at hw
      linarith [hw]
  · have hn128' : 128 ≤ n := by omega
    let x : ℚ := ((n - 128 : ℕ) : ℚ) / ((n + 128 : ℕ) : ℚ)
    have hx0 : 0 ≤ x := by dsimp only [x]; positivity
    have hx : x ≤ 17 / 47 := by
      dsimp only [x]
      rw [div_le_iff₀ (by positivity)]
      norm_num only [Nat.cast_sub hn128', Nat.cast_add, Nat.cast_ofNat]
      have hnq : (n : ℚ) ≤ 200 := by exact_mod_cast hn200
      linarith
    have hx1 : x < 1 := hx.trans_lt (by norm_num)
    have hc := logRatioInterval_contains hx0 hx1
    exact ⟨valid_of_contains hc,
      logRatioInterval_structural_width_le hx0 hx⟩

private theorem highLogTwo_metrics :
    HighIntervalMetrics highLogTwoInterval 1
      (1 / 100000000000000) := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
    norm_num [highLogTwoInterval, RatInterval.Valid, AbsBound, width]

private theorem highLogNatInterval_width_le
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200) :
    width (highLogNatInterval n) ≤ (1 / 10000000000000 : ℚ) := by
  have hratio := highLogNatRatioInterval_valid_and_width hn60 hn200
  unfold highLogNatInterval
  rw [width_add, width_pure_mul 7 highLogTwo_metrics.valid,
    abs_of_nonneg (by norm_num)]
  calc
    7 * width highLogTwoInterval + width (highLogNatRatioInterval n) ≤
        7 * (1 / 100000000000000 : ℚ) +
          1 / 1000000000000000 := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        highLogTwo_metrics.width_le (by norm_num)) hratio.2
    _ ≤ (1 / 10000000000000 : ℚ) := by norm_num

private theorem negLogLengthInterval_width_le :
    width negLogLengthInterval ≤ (1 / 10000000000000 : ℚ) := by
  norm_num [negLogLengthInterval, highLogTwoInterval, logRatioLower,
    logRatioUpper, width, Finset.sum_range_succ]

private theorem highSmallZInterval_structural_bounds
    {n : ℕ} (hn60 : 60 ≤ n) :
    (highSmallZInterval n).Valid ∧
      0 ≤ (highSmallZInterval n).lower ∧
      (highSmallZInterval n).upper ≤ (1 / 1000000 : ℚ) ∧
      width (highSmallZInterval n) ≤
        (1 / 1000000000000000000 : ℚ) := by
  let q : ℚ := n
  let A : ℚ := highLogTwoInterval.lower ^ 2 /
    (16 * piFineInterval.upper ^ 2)
  let B : ℚ := highLogTwoInterval.upper ^ 2 /
    (16 * piFineInterval.lower ^ 2)
  have hq60 : (60 : ℚ) ≤ q := by
    dsimp only [q]
    exact_mod_cast hn60
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq60
  have hq2 : (3600 : ℚ) ≤ q ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := by
    norm_num [A, highLogTwoInterval, piFineInterval]
  have hAB : A ≤ B := by
    norm_num [A, B, highLogTwoInterval, piFineInterval]
  have hBupper : B ≤ (1 / 1000000 : ℚ) * 3600 := by
    norm_num [B, highLogTwoInterval, piFineInterval]
  have hgap : B - A ≤
      (1 / 1000000000000000000 : ℚ) * 3600 := by
    norm_num [A, B, highLogTwoInterval, piFineInterval]
  have hlower : (highSmallZInterval n).lower = A / q ^ 2 := by
    unfold highSmallZInterval
    dsimp only [A, q]
    field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast (by omega : n ≠ 0)]
  have hupper : (highSmallZInterval n).upper = B / q ^ 2 := by
    unfold highSmallZInterval
    dsimp only [B, q]
    field_simp [show (n : ℚ) ≠ 0 by exact_mod_cast (by omega : n ≠ 0)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold RatInterval.Valid
    rw [hlower, hupper]
    exact div_le_div_of_nonneg_right hAB (sq_nonneg q)
  · rw [hlower]
    exact div_nonneg hA0 (sq_nonneg q)
  · rw [hupper, div_le_iff₀ (sq_pos_of_pos hqpos)]
    nlinarith
  · unfold width
    rw [hupper, hlower]
    rw [div_sub_div_same]
    rw [div_le_iff₀ (sq_pos_of_pos hqpos)]
    nlinarith

private theorem highLogOnePlusInterval_structural_metrics
    {n : ℕ} (hn60 : 60 ≤ n) :
    HighIntervalMetrics
      (highLogOnePlusInterval (highSmallZInterval n)) 1
      (1 / 1000000000000) := by
  have hz := highSmallZInterval_structural_bounds hn60
  have hn : n ≠ 0 := by omega
  have hc := highLogOnePlusInterval_contains hz.2.1
    (highSmallZInterval_contains hn)
  have hvalid := valid_of_contains hc
  let l : ℚ := (highSmallZInterval n).lower
  let u : ℚ := (highSmallZInterval n).upper
  have hl0 : 0 ≤ l := hz.2.1
  have hlu : l ≤ u := hz.1
  have hu : u ≤ 1 / 1000000 := hz.2.2.1
  have hwidth : u - l ≤ 1 / 1000000000000000000 := by
    simpa only [l, u, width] using hz.2.2.2
  have hden : 0 < l + 2 := by linarith
  have hsquare : l ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hl0 hlu 2
  have hfrac : l ^ 2 / (l + 2) ≤ u ^ 2 / 2 :=
    div_le_div₀ (sq_nonneg u) hsquare (by norm_num) (by linarith)
  have hupperSq : u ^ 2 / 2 ≤ (1 / 1000000 : ℚ) ^ 2 / 2 := by
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (hl0.trans hlu) hu 2) (by norm_num)
  have hid : u - 2 * l / (l + 2) =
      (u - l) + l ^ 2 / (l + 2) := by
    field_simp [hden.ne']
    ring
  refine ⟨hvalid, ?_, ?_, by norm_num, by norm_num⟩
  · unfold highLogOnePlusInterval AbsBound
    dsimp only
    constructor
    · change -1 ≤ 2 * l / (l + 2)
      have : 0 ≤ 2 * l / (l + 2) := div_nonneg (by positivity) hden.le
      linarith
    · change u ≤ 1
      linarith
  · unfold highLogOnePlusInterval width
    dsimp only
    change u - 2 * l / (l + 2) ≤ _
    rw [hid]
    calc
      (u - l) + l ^ 2 / (l + 2) ≤
          (1 / 1000000000000000000 : ℚ) +
            (1 / 1000000 : ℚ) ^ 2 / 2 :=
        add_le_add hwidth (hfrac.trans hupperSq)
      _ ≤ (1 / 1000000000000 : ℚ) := by norm_num

private theorem highDiagonalLogCoreInterval_width_le
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200) :
    width (highDiagonalLogCoreInterval n) ≤
      (1 / 1000000000000 : ℚ) := by
  have hlogz := highLogOnePlusInterval_structural_metrics hn60
  have htwo := highMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have hdiv := highMetrics_div (m := (2 : ℚ)) hlogz htwo (by norm_num)
    (by simp [RatInterval.pure])
  unfold highDiagonalLogCoreInterval
  rw [width_add, width_add]
  calc
    width (highLogNatInterval n) + width negLogLengthInterval +
        width (highLogOnePlusInterval (highSmallZInterval n) / pure 2) ≤
      (1 / 10000000000000 : ℚ) +
        1 / 10000000000000 + 1 / 2000000000000 := by
      exact add_le_add (add_le_add
        (highLogNatInterval_width_le hn60 hn200)
        negLogLengthInterval_width_le)
        (hdiv.width_le.trans (by norm_num))
    _ ≤ (1 / 1000000000000 : ℚ) := by norm_num

private theorem highMetrics_positivePow
    {I : RatInterval} {B W : ℚ}
    (hI : HighIntervalMetrics I B W) (hI0 : 0 ≤ I.lower) (k : ℕ) :
    HighIntervalMetrics (highPositivePow I k) (B ^ k)
      ((k : ℚ) * B ^ (k - 1) * W) := by
  have hIu0 : 0 ≤ I.upper := hI0.trans hI.valid
  have huB : I.upper ≤ B := hI.absBound.2
  have hpowValid : I.lower ^ k ≤ I.upper ^ k :=
    pow_le_pow_left₀ hI0 hI.valid k
  refine ⟨hpowValid, ?_, ?_, pow_nonneg hI.bound_nonneg k,
    mul_nonneg (mul_nonneg (by positivity)
      (pow_nonneg hI.bound_nonneg (k - 1))) hI.width_nonneg⟩
  · unfold highPositivePow AbsBound
    constructor
    · exact (neg_nonpos.mpr (pow_nonneg hI.bound_nonneg k)).trans
        (pow_nonneg hI0 k)
    · exact pow_le_pow_left₀ hIu0 huB k
  · unfold highPositivePow width
    have habs := abs_pow_sub_pow_le I.upper I.lower k
    rw [abs_of_nonneg (sub_nonneg.mpr hpowValid),
      abs_of_nonneg (sub_nonneg.mpr hI.valid),
      abs_of_nonneg hIu0, abs_of_nonneg hI0,
      max_eq_left hI.valid] at habs
    calc
      I.upper ^ k - I.lower ^ k ≤
          (I.upper - I.lower) * (k : ℚ) * I.upper ^ (k - 1) := habs
      _ ≤ W * (k : ℚ) * B ^ (k - 1) := by
        have hdiff : I.upper - I.lower ≤ W := by
          simpa only [width] using hI.width_le
        have hfirst : (I.upper - I.lower) * (k : ℚ) ≤ W * k :=
          mul_le_mul_of_nonneg_right hdiff (by positivity)
        exact mul_le_mul hfirst (pow_le_pow_left₀ hIu0 huB (k - 1))
          (pow_nonneg hIu0 (k - 1))
          (mul_nonneg hI.width_nonneg (by positivity))
      _ = (k : ℚ) * B ^ (k - 1) * W := by ring

private theorem highYInterval_lower_le_structural (n : ℕ) :
    (1133 / 250 : ℚ) * n ≤ (highYInterval n).lower := by
  unfold highYInterval
  change (1133 / 250 : ℚ) * n ≤
    piFineInterval.lower * n / highLogTwoInterval.upper
  have hcoeff : (1133 / 250 : ℚ) ≤
      piFineInterval.lower / highLogTwoInterval.upper := by
    norm_num [piFineInterval, highLogTwoInterval]
  have hn0 : (0 : ℚ) ≤ n := by positivity
  calc
    (1133 / 250 : ℚ) * n ≤
        (piFineInterval.lower / highLogTwoInterval.upper) * n :=
      mul_le_mul_of_nonneg_right hcoeff hn0
    _ = piFineInterval.lower * n / highLogTwoInterval.upper := by ring

private theorem highYInterval_metrics
    {n : ℕ} (hn200 : n ≤ 200) :
    HighIntervalMetrics (highYInterval n) 1000
      (1 / 50000000000) := by
  let q : ℚ := n
  let C : ℚ := piFineInterval.upper / highLogTwoInterval.lower -
    piFineInterval.lower / highLogTwoInterval.upper
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq200 : q ≤ 200 := by
    dsimp only [q]
    exact_mod_cast hn200
  have hC0 : 0 ≤ C := by
    norm_num [C, piFineInterval, highLogTwoInterval]
  have hC : C ≤ (1 / 10000000000000 : ℚ) := by
    norm_num [C, piFineInterval, highLogTwoInterval]
  have hupperCoeff : piFineInterval.upper / highLogTwoInterval.lower ≤
      (4533 / 1000 : ℚ) := by
    norm_num [piFineInterval, highLogTwoInterval]
  have hupper : (highYInterval n).upper ≤ 1000 := by
    unfold highYInterval
    change piFineInterval.upper * q / highLogTwoInterval.lower ≤ 1000
    calc
      piFineInterval.upper * q / highLogTwoInterval.lower =
          (piFineInterval.upper / highLogTwoInterval.lower) * q := by ring
      _ ≤ (4533 / 1000 : ℚ) * q :=
        mul_le_mul_of_nonneg_right hupperCoeff hq0
      _ ≤ (4533 / 1000 : ℚ) * 200 := by gcongr
      _ ≤ 1000 := by norm_num
  have hwidth : width (highYInterval n) = C * q := by
    unfold highYInterval width
    dsimp only [C, q]
    ring
  refine ⟨valid_of_contains (highYInterval_contains n), ?_, ?_, by norm_num,
    by norm_num⟩
  · unfold AbsBound
    constructor
    · have hl0 : 0 ≤ (highYInterval n).lower := by
        unfold highYInterval
        exact div_nonneg (mul_nonneg (by norm_num [piFineInterval])
          (by positivity)) (by norm_num [highLogTwoInterval])
      linarith
    · exact hupper
  · rw [hwidth]
    calc
      C * q ≤ (1 / 10000000000000 : ℚ) * 200 :=
        mul_le_mul hC hq200 hq0 (by norm_num)
      _ ≤ (1 / 50000000000 : ℚ) := by norm_num

private theorem highYSqInterval_metrics
    {n : ℕ} (hn200 : n ≤ 200) :
    HighIntervalMetrics (highYSqInterval n) 1000000
      (1 / 20000000) := by
  have hy := highYInterval_metrics hn200
  have hy0 : 0 ≤ (highYInterval n).lower := by
    unfold highYInterval
    exact div_nonneg (mul_nonneg (by norm_num [piFineInterval])
      (by positivity)) (by norm_num [highLogTwoInterval])
  have hsq := highMetrics_positiveSquare hy hy0
  simpa only [highYSqInterval] using hsq.weaken (by norm_num) (by norm_num)

private theorem highYSqInterval_lower_le
    {n : ℕ} (hn60 : 60 ≤ n) :
    (70000 : ℚ) ≤ (highYSqInterval n).lower := by
  have hy := highYInterval_lower_le_structural n
  have hnq : (60 : ℚ) ≤ n := by exact_mod_cast hn60
  have hyl : (1133 / 250 : ℚ) * 60 ≤ (highYInterval n).lower := by
    calc
      (1133 / 250 : ℚ) * 60 ≤ (1133 / 250 : ℚ) * n := by gcongr
      _ ≤ (highYInterval n).lower := hy
  unfold highYSqInterval highPositiveSquare
  nlinarith [sq_nonneg ((highYInterval n).lower)]

private theorem highProfileDenInterval_metrics
    {n : ℕ} (hn200 : n ≤ 200) {u : ℚ} (hu : |u| ≤ 2) :
    HighIntervalMetrics (highProfileDenInterval n u) 1000004
      (1 / 20000000) := by
  have hu' := hu
  rw [abs_le] at hu'
  have huSq : |u ^ 2| ≤ (4 : ℚ) := by
    rw [abs_of_nonneg (sq_nonneg u)]
    nlinarith [sq_nonneg (u - 2), sq_nonneg (u + 2)]
  have hU := highMetrics_pure huSq (by norm_num : (0 : ℚ) ≤ 4)
  have hY := highYSqInterval_metrics hn200
  unfold highProfileDenInterval
  simpa using (highMetrics_add hU hY).weaken (by norm_num) (by norm_num)

private theorem highProfileDenInterval_lower_le
    {n : ℕ} (hn60 : 60 ≤ n) (u : ℚ) :
    (70000 : ℚ) ≤ (highProfileDenInterval n u).lower := by
  have hy := highYSqInterval_lower_le hn60
  unfold highProfileDenInterval
  change 70000 ≤ u ^ 2 + (highYSqInterval n).lower
  nlinarith [sq_nonneg u]

private theorem highProfileDenPow_metrics
    {n : ℕ} (hn200 : n ≤ 200) {u : ℚ} (hu : |u| ≤ 2) (k : ℕ) :
    HighIntervalMetrics (highPositivePow (highProfileDenInterval n u) k)
      (1000004 ^ k)
      ((k : ℚ) * 1000004 ^ (k - 1) * (1 / 20000000)) := by
  have hden := highProfileDenInterval_metrics hn200 hu
  have hden0 : 0 ≤ (highProfileDenInterval n u).lower := by
    unfold highProfileDenInterval
    change 0 ≤ u ^ 2 + (highYSqInterval n).lower
    have hy := (highYSqInterval_metrics hn200).valid
    have hyl : 0 ≤ (highYSqInterval n).lower := by
      unfold highYSqInterval highPositiveSquare
      positivity
    positivity
  exact highMetrics_positivePow hden hden0 k

private theorem highProfileDenPow_lower_le
    {n : ℕ} (hn60 : 60 ≤ n) (u : ℚ) (k : ℕ) :
    (70000 : ℚ) ^ k ≤
      (highPositivePow (highProfileDenInterval n u) k).lower := by
  unfold highPositivePow
  exact pow_le_pow_left₀ (by norm_num)
    (highProfileDenInterval_lower_le hn60 u) k

private theorem highProfileInterval_metrics
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200)
    {u : ℚ} (hu : |u| ≤ 2) :
    HighIntervalMetrics (highProfileInterval n u) (1 / 30000)
      (1 / 1000000000000) := by
  have hnum := highMetrics_pure hu (by norm_num : (0 : ℚ) ≤ 2)
  have hden := highProfileDenInterval_metrics hn200 hu
  have hquot := highMetrics_div (m := (70000 : ℚ)) hnum hden
    (by norm_num) (highProfileDenInterval_lower_le hn60 u)
  unfold highProfileInterval
  exact hquot.weaken (by norm_num) (by norm_num)

private theorem highProfileDerivInterval_metrics
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200)
    {u : ℚ} (hu : |u| ≤ 2) :
    HighIntervalMetrics (highProfileDerivInterval n u) (1 / 4000)
      (1 / 1000000000000) := by
  have hu' := hu
  rw [abs_le] at hu'
  have huSq : |u ^ 2| ≤ (4 : ℚ) := by
    rw [abs_of_nonneg (sq_nonneg u)]
    nlinarith [sq_nonneg (u - 2), sq_nonneg (u + 2)]
  have hU := highMetrics_pure huSq (by norm_num : (0 : ℚ) ≤ 4)
  have hY := highYSqInterval_metrics hn200
  have hnum := highMetrics_sub hY hU
  have hden := highProfileDenPow_metrics hn200 hu 2
  have hquot := highMetrics_div (m := (70000 : ℚ) ^ 2) hnum hden
    (by norm_num) (highProfileDenPow_lower_le hn60 u 2)
  unfold highProfileDerivInterval
  exact hquot.weaken (by norm_num) (by norm_num)

private theorem highProfileSecondInterval_metrics
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200)
    {u : ℚ} (hu : |u| ≤ 2) :
    HighIntervalMetrics (highProfileSecondInterval n u) (1 / 10000000)
      (1 / 1000000000000) := by
  have hu' := hu
  rw [abs_le] at hu'
  have huSq : |u ^ 2| ≤ (4 : ℚ) := by
    rw [abs_of_nonneg (sq_nonneg u)]
    nlinarith [sq_nonneg (u - 2), sq_nonneg (u + 2)]
  have hU := highMetrics_pure huSq (by norm_num : (0 : ℚ) ≤ 4)
  have hthree := highMetrics_pure (q := (3 : ℚ)) (B := 3)
    (by norm_num) (by norm_num)
  have hY := highYSqInterval_metrics hn200
  have hinner := highMetrics_sub hU (highMetrics_mul hthree hY)
  have htwou : |2 * u| ≤ (4 : ℚ) := by
    rw [abs_mul]
    norm_num
    linarith [abs_nonneg u]
  have hfactor := highMetrics_pure htwou (by norm_num : (0 : ℚ) ≤ 4)
  have hnum := highMetrics_mul hfactor hinner
  have hden := highProfileDenPow_metrics hn200 hu 3
  have hquot := highMetrics_div (m := (70000 : ℚ) ^ 3) hnum hden
    (by norm_num) (highProfileDenPow_lower_le hn60 u 3)
  unfold highProfileSecondInterval
  exact hquot.weaken (by norm_num) (by norm_num)

private theorem highProfileThirdInterval_metrics
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200)
    {u : ℚ} (hu : |u| ≤ 2) :
    HighIntervalMetrics (highProfileThirdInterval n u) (1 / 1000000)
      (1 / 1000000000000) := by
  have hu' := hu
  rw [abs_le] at hu'
  have huSqLe : u ^ 2 ≤ (4 : ℚ) := by
    nlinarith [sq_nonneg (u - 2), sq_nonneg (u + 2)]
  have huFourth : |u ^ 4| ≤ (16 : ℚ) := by
    rw [abs_of_nonneg (by positivity : (0 : ℚ) ≤ u ^ 4)]
    nlinarith [sq_nonneg (u ^ 2),
      mul_le_mul huSqLe huSqLe (sq_nonneg u) (by norm_num : (0 : ℚ) ≤ 4)]
  have hsixUSq : |6 * u ^ 2| ≤ (24 : ℚ) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
    norm_num
    nlinarith [sq_nonneg (u - 2), sq_nonneg (u + 2)]
  have hU4 := highMetrics_pure huFourth (by norm_num : (0 : ℚ) ≤ 16)
  have hSixUSq := highMetrics_pure hsixUSq (by norm_num : (0 : ℚ) ≤ 24)
  have hY := highYSqInterval_metrics hn200
  have hYSq0 : 0 ≤ (highYSqInterval n).lower := by
    unfold highYSqInterval highPositiveSquare
    positivity
  have hY2 := highMetrics_positiveSquare hY hYSq0
  have hpoly := highMetrics_add
    (highMetrics_sub hU4 (highMetrics_mul hSixUSq hY)) hY2
  have hnegSix := highMetrics_pure (q := (-6 : ℚ)) (B := 6)
    (by norm_num) (by norm_num)
  have hnum := highMetrics_mul hnegSix hpoly
  have hden := highProfileDenPow_metrics hn200 hu 4
  have hquot := highMetrics_div (m := (70000 : ℚ) ^ 4) hnum hden
    (by norm_num) (highProfileDenPow_lower_le hn60 u 4)
  unfold highProfileThirdInterval
  exact hquot.weaken (by norm_num) (by norm_num)

private theorem mul_lower_eq_of_nonneg
    {I J : RatInterval} (hI0 : 0 ≤ I.lower) (hJ0 : 0 ≤ J.lower)
    (hI : I.Valid) (hJ : J.Valid) :
    (I * J).lower = I.lower * J.lower := by
  have hIu0 : 0 ≤ I.upper := hI0.trans hI
  have hJu0 : 0 ≤ J.upper := hJ0.trans hJ
  change min (min (I.lower * J.lower) (I.lower * J.upper))
    (min (I.upper * J.lower) (I.upper * J.upper)) = I.lower * J.lower
  apply le_antisymm
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · apply le_min
    · exact le_min (le_rfl) (mul_le_mul_of_nonneg_left hJ hI0)
    · exact le_min (mul_le_mul_of_nonneg_right hI hJ0)
        (mul_le_mul hI hJ hJ0 hIu0)

private theorem sqrtTwoInterval_metrics :
    HighIntervalMetrics sqrtTwoInterval 2
      (1 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num⟩ <;>
    norm_num [sqrtTwoInterval, RatInterval.Valid, AbsBound, width]

private theorem highKappaSqInterval_metrics
    {n : ℕ} (hn200 : n ≤ 200) :
    HighIntervalMetrics (highKappaSqInterval n) 4000000
      (1 / 5000000) := by
  have hfour := highMetrics_pure (q := (4 : ℚ)) (B := 4)
    (by norm_num) (by norm_num)
  have hy := highYSqInterval_metrics hn200
  unfold highKappaSqInterval
  simpa using (highMetrics_mul hfour hy).weaken (by norm_num) (by norm_num)

private theorem highKappaSqInterval_lower_le
    {n : ℕ} (hn60 : 60 ≤ n) :
    (280000 : ℚ) ≤ (highKappaSqInterval n).lower := by
  have hy := highYSqInterval_lower_le hn60
  have hyv := valid_of_contains (highYSqInterval_contains (by omega : n ≠ 0))
  unfold highKappaSqInterval
  have hy0 : 0 ≤ (highYSqInterval n).lower := by linarith
  rw [mul_lower_eq_of_nonneg (by simp [RatInterval.pure]) hy0
    (valid_pure 4) hyv]
  change 280000 ≤ 4 * (highYSqInterval n).lower
  linarith

private theorem highDerivativeMainInterval_metrics
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200) :
    HighIntervalMetrics (highDerivativeMainInterval n) (1 / 5000)
      (2 / 1000000000000) := by
  have hp := highProfileInterval_metrics hn60 hn200
    (u := (5 / 4 : ℚ)) (by norm_num)
  have hd := highProfileDerivInterval_metrics hn60 hn200
    (u := (5 / 4 : ℚ)) (by norm_num)
  have hs := highProfileSecondInterval_metrics hn60 hn200
    (u := (5 / 4 : ℚ)) (by norm_num)
  have htwo := highMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have htwelve := highMetrics_pure (q := (12 : ℚ)) (B := 12)
    (by norm_num) (by norm_num)
  have hd2 := highMetrics_div (m := (2 : ℚ)) hd htwo
    (by norm_num) (by simp [RatInterval.pure])
  have hs12 := highMetrics_div (m := (12 : ℚ)) hs htwelve
    (by norm_num) (by simp [RatInterval.pure])
  have hcombine := highMetrics_sub
    (highMetrics_add (highMetrics_neg hp) hd2) hs12
  unfold highDerivativeMainInterval
  exact hcombine.weaken (by norm_num) (by norm_num)

private theorem highRampInterval_metrics
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200) :
    HighIntervalMetrics (highRampInterval n) (1 / 1000)
      (1 / 1000000000000) := by
  let L := highLogTwoInterval
  let p := highKappaSqInterval n
  let a := pure (-1 / 2 : ℚ)
  let aSq := pure (1 / 4 : ℚ)
  have hL : HighIntervalMetrics L 1 (1 / 100000000000000) := by
    simpa only [L] using highLogTwo_metrics
  have hp : HighIntervalMetrics p 4000000 (1 / 5000000) := by
    simpa only [p] using highKappaSqInterval_metrics hn200
  have ha := highMetrics_pure (q := (-1 / 2 : ℚ)) (B := 1 / 2)
    (by norm_num) (by norm_num)
  have haSq := highMetrics_pure (q := (1 / 4 : ℚ)) (B := 1 / 4)
    (by norm_num) (by norm_num)
  have hone := highMetrics_pure (q := (1 : ℚ)) (B := 1)
    (by norm_num) (by norm_num)
  have htwo := highMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have hA := highMetrics_add
    (highMetrics_sub sqrtTwoInterval_metrics hone)
    (highMetrics_mul ha hL)
  have hB := highMetrics_sub haSq hp
  have hfirst := highMetrics_mul hA hB
  have hsecond := highMetrics_mul
    (highMetrics_mul (highMetrics_mul htwo ha) hp) hL
  have hnum := highMetrics_add hfirst hsecond
  have hsum := highMetrics_add haSq hp
  have hsum0 : 0 ≤ (aSq + p).lower := by
    have hpLower := highKappaSqInterval_lower_le hn60
    change 0 ≤ (1 / 4 : ℚ) + p.lower
    linarith
  have hsumLower : (280000 : ℚ) ≤ (aSq + p).lower := by
    have hpLower := highKappaSqInterval_lower_le hn60
    change 280000 ≤ (1 / 4 : ℚ) + p.lower
    linarith
  have hsq := highMetrics_positiveSquare hsum hsum0
  have hden := highMetrics_mul hL hsq
  have hL0 : 0 ≤ L.lower := by norm_num [L, highLogTwoInterval]
  have hsq0 : 0 ≤ (highPositiveSquare (aSq + p)).lower := by
    unfold highPositiveSquare
    positivity
  have hdenEq := mul_lower_eq_of_nonneg hL0 hsq0 hL.valid hsq.valid
  have hdenLower : (30000000000 : ℚ) ≤
      (L * highPositiveSquare (aSq + p)).lower := by
    rw [hdenEq]
    have hLhalf : (1 / 2 : ℚ) ≤ L.lower := by
      norm_num [L, highLogTwoInterval]
    have hsqLower : (280000 : ℚ) ^ 2 ≤
        (highPositiveSquare (aSq + p)).lower := by
      unfold highPositiveSquare
      exact pow_le_pow_left₀ (by norm_num) hsumLower 2
    nlinarith [mul_le_mul hLhalf hsqLower (by positivity)
      hL0]
  have hquot := highMetrics_div (m := (30000000000 : ℚ)) hnum hden
    (by norm_num) hdenLower
  unfold highRampInterval
  dsimp only [L, p, a, aSq] at hquot ⊢
  exact hquot.weaken (by norm_num) (by norm_num)

private theorem highNegQMainInterval_metrics
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200) :
    HighIntervalMetrics (highNegQMainInterval n) 1
      (1 / 1000000000000) := by
  have hthree := highMetrics_pure (q := (3 : ℚ)) (B := 3)
    (by norm_num) (by norm_num)
  have hL := highLogTwo_metrics
  have hp := highKappaSqInterval_metrics hn200
  have h3s := highMetrics_mul hthree sqrtTwoInterval_metrics
  have h3sL := highMetrics_mul h3s hL
  have hden := highMetrics_mul h3sL hp
  have hthree0 : 0 ≤ (pure 3).lower := by simp [RatInterval.pure]
  have hs0 : 0 ≤ sqrtTwoInterval.lower := by norm_num [sqrtTwoInterval]
  have hL0 : 0 ≤ highLogTwoInterval.lower := by
    norm_num [highLogTwoInterval]
  have hp0 : 0 ≤ (highKappaSqInterval n).lower := by
    linarith [highKappaSqInterval_lower_le hn60]
  have heq3s := mul_lower_eq_of_nonneg hthree0 hs0
    hthree.valid sqrtTwoInterval_metrics.valid
  have h3s0 : 0 ≤ (pure 3 * sqrtTwoInterval).lower := by
    rw [heq3s]
    positivity
  have heq3sL := mul_lower_eq_of_nonneg h3s0 hL0 h3s.valid hL.valid
  have h3sL0 : 0 ≤
      (pure 3 * sqrtTwoInterval * highLogTwoInterval).lower := by
    rw [heq3sL]
    positivity
  have heqDen := mul_lower_eq_of_nonneg h3sL0 hp0 h3sL.valid hp.valid
  have hdenLower : (400000 : ℚ) ≤
      (pure 3 * sqrtTwoInterval * highLogTwoInterval *
        highKappaSqInterval n).lower := by
    rw [heqDen, heq3sL, heq3s]
    have hpLower := highKappaSqInterval_lower_le hn60
    norm_num [RatInterval.pure, sqrtTwoInterval, highLogTwoInterval] at ⊢
    nlinarith
  have htwo := highMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have hquot := highMetrics_div (m := (400000 : ℚ)) htwo hden
    (by norm_num) hdenLower
  unfold highNegQMainInterval
  exact hquot.weaken (by norm_num) (by norm_num)

private theorem highDerivativeQuotientInterval_metrics
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200) :
    HighIntervalMetrics
      (highDerivativeMainInterval n / (pure 2 * highLogTwoInterval)) 1
      (3 / 1000000000000) := by
  have hnum := highDerivativeMainInterval_metrics hn60 hn200
  have htwo := highMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have hden := highMetrics_mul htwo highLogTwo_metrics
  have hdenLower : (1 : ℚ) ≤ (pure 2 * highLogTwoInterval).lower := by
    rw [mul_lower_eq_of_nonneg (by simp [RatInterval.pure])
      (by norm_num [highLogTwoInterval]) htwo.valid highLogTwo_metrics.valid]
    norm_num [RatInterval.pure, highLogTwoInterval]
  have hquot := highMetrics_div (m := (1 : ℚ)) hnum hden
    (by norm_num) hdenLower
  exact hquot.weaken (by norm_num) (by norm_num)

private theorem highErrorRadii_structural_bounds
    {n : ℕ} (hn60 : 60 ≤ n) :
    highDigammaRadius n ≤ (1 / 1000000000000 : ℚ) ∧
      highDerivativeRadius n ≤ (340 / 1000000000000 : ℚ) ∧
      highQRadius n ≤ (284 / 1000000000000 : ℚ) := by
  let y : ℚ := (highYInterval n).lower
  let y0 : ℚ := (1133 / 250 : ℚ) * 60
  have hnq : (60 : ℚ) ≤ n := by exact_mod_cast hn60
  have hy : y0 ≤ y := by
    dsimp only [y, y0]
    calc
      (1133 / 250 : ℚ) * 60 ≤ (1133 / 250 : ℚ) * n := by gcongr
      _ ≤ (highYInterval n).lower := highYInterval_lower_le_structural n
  have hy0 : 0 < y0 := by norm_num [y0]
  have hypos : 0 < y := hy0.trans_le hy
  have hp4 : y0 ^ 4 ≤ y ^ 4 := pow_le_pow_left₀ hy0.le hy 4
  have hp5 : y0 ^ 5 ≤ y ^ 5 := pow_le_pow_left₀ hy0.le hy 5
  constructor
  · unfold highDigammaRadius
    change 4 / (3 * y ^ 5) ≤ _
    calc
      4 / (3 * y ^ 5) ≤ 4 / (3 * y0 ^ 5) :=
        div_le_div_of_nonneg_left (by norm_num)
          (mul_pos (by norm_num) (pow_pos hy0 5))
          (mul_le_mul_of_nonneg_left hp5 (by norm_num))
      _ ≤ (1 / 1000000000000 : ℚ) := by norm_num [y0]
  · constructor
    · unfold highDerivativeRadius
      change 5 / (4 * highLogTwoInterval.lower * y ^ 4) ≤ _
      calc
        5 / (4 * highLogTwoInterval.lower * y ^ 4) ≤
            5 / (4 * highLogTwoInterval.lower * y0 ^ 4) :=
          div_le_div_of_nonneg_left (by norm_num)
            (by norm_num [highLogTwoInterval, y0])
            (mul_le_mul_of_nonneg_left hp4
              (by norm_num [highLogTwoInterval]))
        _ ≤ (340 / 1000000000000 : ℚ) := by
          norm_num [highLogTwoInterval, y0]
    · unfold highQRadius
      change 425 /
        (18 * sqrtTwoInterval.lower * highLogTwoInterval.lower *
          (2 * y) ^ 4) ≤ _
      have hp2 : (2 * y0) ^ 4 ≤ (2 * y) ^ 4 :=
        pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_left hy (by norm_num)) 4
      calc
        425 /
            (18 * sqrtTwoInterval.lower * highLogTwoInterval.lower *
              (2 * y) ^ 4) ≤
          425 /
            (18 * sqrtTwoInterval.lower * highLogTwoInterval.lower *
              (2 * y0) ^ 4) :=
            div_le_div_of_nonneg_left (by norm_num)
              (by norm_num [sqrtTwoInterval, highLogTwoInterval, y0])
              (mul_le_mul_of_nonneg_left hp2
                (by norm_num [sqrtTwoInterval, highLogTwoInterval]))
        _ ≤ (284 / 1000000000000 : ℚ) := by
          norm_num [sqrtTwoInterval, highLogTwoInterval, y0]

private theorem highDiagonalUniformErrorInterval_width_le
    {n : ℕ} (hn60 : 60 ≤ n) :
    width (highDiagonalUniformErrorInterval n) ≤
      (966 / 1000000000000 : ℚ) := by
  have h := highErrorRadii_structural_bounds hn60
  unfold highDiagonalUniformErrorInterval width
  dsimp only
  calc
    (highDigammaRadius n + highDerivativeRadius n) -
        -(highDigammaRadius n + highDerivativeRadius n + highQRadius n) =
      2 * highDigammaRadius n + 2 * highDerivativeRadius n +
        highQRadius n := by ring
    _ ≤ 2 * (1 / 1000000000000 : ℚ) +
        2 * (340 / 1000000000000 : ℚ) +
          284 / 1000000000000 := by
      gcongr
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    _ = (966 / 1000000000000 : ℚ) := by norm_num

private theorem highDiagonalUniformMainInterval_width_le
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200) :
    width (highDiagonalUniformMainInterval n) ≤
      (8 / 1000000000000 : ℚ) := by
  have hramp := highRampInterval_metrics hn60 hn200
  have hp := highProfileInterval_metrics hn60 hn200
    (u := (1 / 4 : ℚ)) (by norm_num)
  have hd := highProfileDerivInterval_metrics hn60 hn200
    (u := (1 / 4 : ℚ)) (by norm_num)
  have ht := highProfileThirdInterval_metrics hn60 hn200
    (u := (1 / 4 : ℚ)) (by norm_num)
  have hderiv := highDerivativeQuotientInterval_metrics hn60 hn200
  have hq := highNegQMainInterval_metrics hn60 hn200
  have htwo := highMetrics_pure (q := (2 : ℚ)) (B := 2)
    (by norm_num) (by norm_num)
  have htwelve := highMetrics_pure (q := (12 : ℚ)) (B := 12)
    (by norm_num) (by norm_num)
  have hsevenTwenty := highMetrics_pure (q := (720 : ℚ)) (B := 720)
    (by norm_num) (by norm_num)
  have htwoRamp := highMetrics_mul htwo hramp
  have hpTwo := highMetrics_div (m := (2 : ℚ)) hp htwo
    (by norm_num) (by simp [RatInterval.pure])
  have hdTwelve := highMetrics_div (m := (12 : ℚ)) hd htwelve
    (by norm_num) (by simp [RatInterval.pure])
  have htSevenTwenty := highMetrics_div (m := (720 : ℚ)) ht hsevenTwenty
    (by norm_num) (by simp [RatInterval.pure])
  unfold highDiagonalUniformMainInterval
  simp only [width_add, width_sub]
  linarith [highDiagonalLogCoreInterval_width_le hn60 hn200,
    htwoRamp.width_le, hpTwo.width_le, hdTwelve.width_le,
    htSevenTwenty.width_le, hderiv.width_le, hq.width_le]

/-- Direct high-frequency rational enclosure obtained from the uniform main
term and its three analytic remainder bounds. -/
def yoshidaFactorTwoCleanHighDiagonalTarget (n : ℕ) : RatInterval :=
  highDiagonalUniformMainInterval n + highDiagonalUniformErrorInterval n

/-- The direct target contains the actual diagonal moment at every positive
mode; the high-band restriction is needed only for the width certificate. -/
theorem yoshidaFactorTwoCleanHighDiagonalTarget_contains
    {n : ℕ} (hn : n ≠ 0) :
    (yoshidaFactorTwoCleanHighDiagonalTarget n).Contains
      (yoshidaDiagonalMoment n) := by
  have hm := highDiagonalUniformMainInterval_contains hn
  have he := highDiagonalUniformErrorInterval_contains hn
  unfold yoshidaFactorTwoCleanHighDiagonalTarget
  convert contains_add hm he using 1
  ring

/-- Exact kernel-checked width certificate for the full clean high diagonal
band.  The direct high-frequency target is already narrow enough from mode
`60`, so this strictly contains the requested band `64, ..., 200`. -/
theorem yoshidaFactorTwoCleanHighDiagonalTarget_width_le
    {n : ℕ} (hn60 : 60 ≤ n) (hn200 : n ≤ 200) :
    width (yoshidaFactorTwoCleanHighDiagonalTarget n) ≤
      (1 / 1000000000 : ℚ) := by
  unfold yoshidaFactorTwoCleanHighDiagonalTarget
  rw [width_add]
  calc
    width (highDiagonalUniformMainInterval n) +
        width (highDiagonalUniformErrorInterval n) ≤
      (8 / 1000000000000 : ℚ) + 966 / 1000000000000 :=
        add_le_add (highDiagonalUniformMainInterval_width_le hn60 hn200)
          (highDiagonalUniformErrorInterval_width_le hn60)
    _ ≤ (1 / 1000000000 : ℚ) := by norm_num

/-- The immediately preceding mode misses the `10⁻⁹` target, certifying that
`60` is the exact cutoff for this direct rational enclosure family. -/
theorem yoshidaFactorTwoCleanHighDiagonalTarget_59_width_gt :
    (1 / 1000000000 : ℚ) <
      width (yoshidaFactorTwoCleanHighDiagonalTarget 59) := by
  have hmain : 0 ≤ width (highDiagonalUniformMainInterval 59) :=
    width_nonneg (valid_of_contains
      (highDiagonalUniformMainInterval_contains (by norm_num)))
  have herr : (1 / 1000000000 : ℚ) <
      width (highDiagonalUniformErrorInterval 59) := by
    norm_num [highDiagonalUniformErrorInterval, highDigammaRadius,
      highDerivativeRadius, highQRadius, highYInterval,
      highLogTwoInterval, sqrtTwoInterval, piFineInterval, width]
  unfold yoshidaFactorTwoCleanHighDiagonalTarget
  rw [width_add]
  linarith

/-- Complete direct clean high-diagonal enclosure and width obligation. -/
def YoshidaFactorTwoCleanHighDiagonalTargetEnclosures : Prop :=
  ∀ n, 60 ≤ n → n ≤ 200 →
    (yoshidaFactorTwoCleanHighDiagonalTarget n).Contains
        (yoshidaDiagonalMoment n) ∧
      width (yoshidaFactorTwoCleanHighDiagonalTarget n) ≤
        (1 / 1000000000 : ℚ)

/-- The direct analytic targets discharge every high-diagonal enclosure and
width certificate from mode `60` through mode `200`. -/
theorem yoshidaFactorTwoCleanHighDiagonalTargetEnclosures :
    YoshidaFactorTwoCleanHighDiagonalTargetEnclosures := by
  intro n hn60 hn200
  exact ⟨yoshidaFactorTwoCleanHighDiagonalTarget_contains (by omega),
    yoshidaFactorTwoCleanHighDiagonalTarget_width_le hn60 hn200⟩

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoCleanHighDiagonalEnclosures
