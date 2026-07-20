import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaDiagonalDigammaHighBound
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArithmeticHodge.Analysis.YoshidaQuarterVerticalDigammaHighEnclosures

noncomputable section

open ArithmeticHodge.Analysis
open DigammaTrapezoid
open RatInterval
open YoshidaDiagonalDigammaHighBound
open YoshidaDiagonalUniformIdentity
open YoshidaOddGramPrefix

/-!
# High-frequency quarter-line digamma residual enclosures

The corrected trapezoid estimate for the quarter-line digamma separates its
only transcendental main term,

`log (1 / 16 + y^2) / 2`,

from three rational profiles and an `O(y^-5)` remainder.  This file encloses
that residual directly.  The result composes with any independently certified
logarithm enclosure without duplicating logarithm approximation work.
-/

private def highLogTwoInterval : RatInterval :=
  ⟨69314718055994 / 100000000000000,
    69314718055995 / 100000000000000⟩

private theorem highLogTwoInterval_contains :
    highLogTwoInterval.Contains yoshidaLength := by
  have hlo := Real.sum_range_le_log_div
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 18
  have hup := Real.log_div_le_sum_range_add
    (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 18
  constructor <;>
    norm_num [highLogTwoInterval, yoshidaLength,
      Finset.sum_range_succ] at hlo hup ⊢ <;> linarith

private def highYInterval (n : ℕ) : RatInterval :=
  ⟨YoshidaSineMomentEnclosures.piFineInterval.lower * n /
      highLogTwoInterval.upper,
    YoshidaSineMomentEnclosures.piFineInterval.upper * n /
      highLogTwoInterval.lower⟩

private theorem highYInterval_contains (n : ℕ) :
    (highYInterval n).Contains (yoshidaY n) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnum0 : 0 ≤ Real.pi * (n : ℝ) :=
    mul_nonneg Real.pi_pos.le hn0
  have hnumLo : (YoshidaSineMomentEnclosures.piFineInterval.lower : ℝ) *
      (n : ℝ) ≤
      Real.pi * (n : ℝ) :=
    mul_le_mul_of_nonneg_right
      YoshidaSineMomentEnclosures.piFineInterval_contains.1 hn0
  have hnumHi : Real.pi * (n : ℝ) ≤
      (YoshidaSineMomentEnclosures.piFineInterval.upper : ℝ) *
        (n : ℝ) :=
    mul_le_mul_of_nonneg_right
      YoshidaSineMomentEnclosures.piFineInterval_contains.2 hn0
  have hLlo : (0 : ℝ) < (highLogTwoInterval.lower : ℚ) := by
    norm_num [highLogTwoInterval]
  have hLup : yoshidaLength ≤
      (highLogTwoInterval.upper : ℚ) := highLogTwoInterval_contains.2
  have hLloLe : (highLogTwoInterval.lower : ℚ) ≤
      yoshidaLength := highLogTwoInterval_contains.1
  have hyEq : yoshidaY n =
      Real.pi * (n : ℝ) / yoshidaLength := by
    unfold yoshidaY yoshidaKappa
    ring
  rw [hyEq]
  unfold highYInterval
  constructor
  · norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    exact div_le_div₀ hnum0 hnumLo yoshidaLength_pos hLup
  · norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    exact div_le_div₀
      (mul_nonneg (by
        norm_num [YoshidaSineMomentEnclosures.piFineInterval]) hn0)
      hnumHi hLlo hLloLe

private theorem highYInterval_lower_pos
    {n : ℕ} (hn : n ≠ 0) :
    0 < (highYInterval n).lower := by
  unfold highYInterval YoshidaSineMomentEnclosures.piFineInterval
    highLogTwoInterval
  positivity

private theorem highYInterval_valid (n : ℕ) :
    (highYInterval n).Valid :=
  valid_of_contains (highYInterval_contains n)

private theorem highYInterval_lower_ge_four_mul (n : ℕ) :
    (4 : ℚ) * n ≤ (highYInterval n).lower := by
  have hcoef : (4 : ℚ) ≤
      YoshidaSineMomentEnclosures.piFineInterval.lower /
        highLogTwoInterval.upper := by
    norm_num [YoshidaSineMomentEnclosures.piFineInterval,
      highLogTwoInterval]
  unfold highYInterval
  calc
    (4 : ℚ) * n ≤
        (YoshidaSineMomentEnclosures.piFineInterval.lower /
          highLogTwoInterval.upper) * n :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = YoshidaSineMomentEnclosures.piFineInterval.lower * n /
        highLogTwoInterval.upper := by ring

private theorem highYInterval_upper_le_five_mul (n : ℕ) :
    (highYInterval n).upper ≤ (5 : ℚ) * n := by
  have hcoef :
      YoshidaSineMomentEnclosures.piFineInterval.upper /
          highLogTwoInterval.lower ≤ (5 : ℚ) := by
    norm_num [YoshidaSineMomentEnclosures.piFineInterval,
      highLogTwoInterval]
  unfold highYInterval
  calc
    YoshidaSineMomentEnclosures.piFineInterval.upper * n /
        highLogTwoInterval.lower =
      (YoshidaSineMomentEnclosures.piFineInterval.upper /
        highLogTwoInterval.lower) * n := by ring
    _ ≤ (5 : ℚ) * n :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)

private theorem highYInterval_width_le (n : ℕ) :
    width (highYInterval n) ≤
      (n : ℚ) / 15000000000000 := by
  have hcoef :
      YoshidaSineMomentEnclosures.piFineInterval.upper /
          highLogTwoInterval.lower -
        YoshidaSineMomentEnclosures.piFineInterval.lower /
          highLogTwoInterval.upper ≤
      (1 / 15000000000000 : ℚ) := by
    norm_num [YoshidaSineMomentEnclosures.piFineInterval,
      highLogTwoInterval]
  change
    YoshidaSineMomentEnclosures.piFineInterval.upper * n /
          highLogTwoInterval.lower -
        YoshidaSineMomentEnclosures.piFineInterval.lower * n /
          highLogTwoInterval.upper ≤
      (n : ℚ) / 15000000000000
  calc
    YoshidaSineMomentEnclosures.piFineInterval.upper * n /
          highLogTwoInterval.lower -
        YoshidaSineMomentEnclosures.piFineInterval.lower * n /
          highLogTwoInterval.upper =
      (YoshidaSineMomentEnclosures.piFineInterval.upper /
          highLogTwoInterval.lower -
        YoshidaSineMomentEnclosures.piFineInterval.lower /
          highLogTwoInterval.upper) * n := by ring
    _ ≤ (1 / 15000000000000 : ℚ) * n :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (n : ℚ) / 15000000000000 := by ring

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

private def highPositivePow (I : RatInterval) (k : ℕ) : RatInterval :=
  ⟨I.lower ^ k, I.upper ^ k⟩

private theorem highPow_sub_pow_le_mul
    {a b B : ℚ} (hb0 : 0 ≤ b) (hba : b ≤ a) (haB : a ≤ B)
    (p : ℕ) :
    a ^ p - b ^ p ≤ (p : ℚ) * B ^ (p - 1) * (a - b) := by
  have ha0 : 0 ≤ a := hb0.trans hba
  have hB0 : 0 ≤ B := ha0.trans haB
  induction p with
  | zero => simp
  | succ p ih =>
      have hpow : b ^ p ≤ a ^ p := pow_le_pow_left₀ hb0 hba p
      have hpowB : a ^ p ≤ B ^ p := pow_le_pow_left₀ ha0 haB p
      have hdiff : 0 ≤ a - b := sub_nonneg.mpr hba
      have hpowdiff : 0 ≤ a ^ p - b ^ p := sub_nonneg.mpr hpow
      calc
        a ^ (p + 1) - b ^ (p + 1) =
            a ^ p * (a - b) + b * (a ^ p - b ^ p) := by ring
        _ ≤ B ^ p * (a - b) +
            B * ((p : ℚ) * B ^ (p - 1) * (a - b)) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right hpowB hdiff)
            (mul_le_mul (hba.trans haB) ih hpowdiff hB0)
        _ = ((p + 1 : ℕ) : ℚ) * B ^ ((p + 1 : ℕ) - 1) *
            (a - b) := by
          push_cast
          cases p
          · simp
          · simp
            ring

private theorem highPositivePow_valid
    {I : RatInterval} (hI0 : 0 ≤ I.lower) (hI : I.Valid) (p : ℕ) :
    (highPositivePow I p).Valid := by
  exact pow_le_pow_left₀ hI0 hI p

private theorem highPositivePow_width_le
    {I : RatInterval} {B W : ℚ} (hI0 : 0 ≤ I.lower) (hI : I.Valid)
    (hupper : I.upper ≤ B) (hwidth : width I ≤ W) (p : ℕ) :
    width (highPositivePow I p) ≤
      (p : ℚ) * B ^ (p - 1) * W := by
  change I.upper ^ p - I.lower ^ p ≤ _
  calc
    I.upper ^ p - I.lower ^ p ≤
        (p : ℚ) * B ^ (p - 1) * (I.upper - I.lower) :=
      highPow_sub_pow_le_mul hI0 hI hupper p
    _ ≤ (p : ℚ) * B ^ (p - 1) * W := by
      exact mul_le_mul_of_nonneg_left hwidth
        (mul_nonneg (Nat.cast_nonneg p) (pow_nonneg (by
          exact (hI0.trans hI).trans hupper) _))

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

private def highYSqInterval (n : ℕ) : RatInterval :=
  highPositiveSquare (highYInterval n)

private theorem highYSqInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (highYSqInterval n).Contains (yoshidaY n ^ 2) := by
  exact highPositiveSquare_contains (highYInterval_lower_pos hn).le
    (highYInterval_contains n)

private theorem highYSqInterval_valid (n : ℕ) :
    (highYSqInterval n).Valid := by
  change (highPositivePow (highYInterval n) 2).Valid
  exact highPositivePow_valid
    ((show (0 : ℚ) ≤ 4 * n by positivity).trans
      (highYInterval_lower_ge_four_mul n))
    (highYInterval_valid n) 2

private theorem highYSqInterval_lower_ge (n : ℕ) :
    (16 : ℚ) * n ^ 2 ≤ (highYSqInterval n).lower := by
  have h := pow_le_pow_left₀
    (show (0 : ℚ) ≤ 4 * n by positivity)
    (highYInterval_lower_ge_four_mul n) 2
  change (16 : ℚ) * n ^ 2 ≤ (highYInterval n).lower ^ 2
  nlinarith

private theorem highYSqInterval_upper_le (n : ℕ) :
    (highYSqInterval n).upper ≤ (25 : ℚ) * n ^ 2 := by
  have h := pow_le_pow_left₀
    (show (0 : ℚ) ≤ (highYInterval n).upper by
      exact (show (0 : ℚ) ≤ 4 * n by positivity).trans
        ((highYInterval_lower_ge_four_mul n).trans
          (highYInterval_valid n)))
    (highYInterval_upper_le_five_mul n) 2
  change (highYInterval n).upper ^ 2 ≤ (25 : ℚ) * n ^ 2
  nlinarith

private theorem highYSqInterval_width_le (n : ℕ) :
    width (highYSqInterval n) ≤
      (n : ℚ) ^ 2 / 1500000000000 := by
  have h := highPositivePow_width_le
    ((show (0 : ℚ) ≤ 4 * n by positivity).trans
      (highYInterval_lower_ge_four_mul n))
    (highYInterval_valid n) (highYInterval_upper_le_five_mul n)
    (highYInterval_width_le n) 2
  change width (highPositivePow (highYInterval n) 2) ≤
    (n : ℚ) ^ 2 / 1500000000000
  calc
    width (highPositivePow (highYInterval n) 2) ≤
        (2 : ℚ) * ((5 : ℚ) * n) ^ (2 - 1) *
          ((n : ℚ) / 15000000000000) := h
    _ = (n : ℚ) ^ 2 / 1500000000000 := by ring

private def highProfileDenInterval (n : ℕ) (u : ℚ) : RatInterval :=
  pure (u ^ 2) + highYSqInterval n

private theorem highQuarterDenInterval_valid (n : ℕ) :
    (highProfileDenInterval n (1 / 4)).Valid := by
  exact valid_add (valid_pure _) (highYSqInterval_valid n)

private theorem highQuarterDenInterval_lower_ge (n : ℕ) :
    (16 : ℚ) * n ^ 2 ≤
      (highProfileDenInterval n (1 / 4)).lower := by
  change (16 : ℚ) * n ^ 2 ≤
    (1 / 4 : ℚ) ^ 2 + (highYSqInterval n).lower
  exact (highYSqInterval_lower_ge n).trans
    (le_add_of_nonneg_left (by norm_num))

private theorem highQuarterDenInterval_upper_le
    {n : ℕ} (hn : 1 ≤ n) :
    (highProfileDenInterval n (1 / 4)).upper ≤
      (26 : ℚ) * n ^ 2 := by
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  change (1 / 4 : ℚ) ^ 2 + (highYSqInterval n).upper ≤
    (26 : ℚ) * n ^ 2
  nlinarith [highYSqInterval_upper_le n, sq_nonneg ((n : ℚ) - 1)]

private theorem highQuarterDenInterval_width_le (n : ℕ) :
    width (highProfileDenInterval n (1 / 4)) ≤
      (n : ℚ) ^ 2 / 1500000000000 := by
  rw [highProfileDenInterval, width_add, width_pure, zero_add]
  exact highYSqInterval_width_le n

private theorem highQuarterDenPow_valid
    {n p : ℕ} :
    (highPositivePow (highProfileDenInterval n (1 / 4)) p).Valid := by
  exact highPositivePow_valid
    (show (0 : ℚ) ≤ (highProfileDenInterval n (1 / 4)).lower by
      exact (by positivity : (0 : ℚ) ≤ 16 * n ^ 2).trans
        (highQuarterDenInterval_lower_ge n))
    (highQuarterDenInterval_valid n) p

private theorem highQuarterDenPow_lower_ge (n p : ℕ) :
    ((16 : ℚ) * n ^ 2) ^ p ≤
      (highPositivePow (highProfileDenInterval n (1 / 4)) p).lower := by
  exact pow_le_pow_left₀ (by positivity)
    (highQuarterDenInterval_lower_ge n) p

private theorem highQuarterDenPow_width_le
    {n p : ℕ} (hn : 1 ≤ n) :
    width (highPositivePow (highProfileDenInterval n (1 / 4)) p) ≤
      (p : ℚ) * ((26 : ℚ) * n ^ 2) ^ (p - 1) *
        ((n : ℚ) ^ 2 / 1500000000000) := by
  exact highPositivePow_width_le
    (show (0 : ℚ) ≤ (highProfileDenInterval n (1 / 4)).lower by
      exact (by positivity : (0 : ℚ) ≤ 16 * n ^ 2).trans
        (highQuarterDenInterval_lower_ge n))
    (highQuarterDenInterval_valid n) (highQuarterDenInterval_upper_le hn)
    (highQuarterDenInterval_width_le n) p

private theorem highProfileDenInterval_contains
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    (highProfileDenInterval n u).Contains
      ((u : ℝ) ^ 2 + yoshidaY n ^ 2) := by
  have huSq : (pure (u ^ 2)).Contains ((u : ℝ) ^ 2) := by
    norm_num [Contains, RatInterval.pure]
  exact contains_add huSq (highYSqInterval_contains hn)

private theorem highProfileDenInterval_lower_pos
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    0 < (highProfileDenInterval n u).lower := by
  unfold highProfileDenInterval highYSqInterval highPositiveSquare
    highYInterval
  change 0 < u ^ 2 +
    (YoshidaSineMomentEnclosures.piFineInterval.lower * n /
      highLogTwoInterval.upper) ^ 2
  have hyn : 0 <
      YoshidaSineMomentEnclosures.piFineInterval.lower * n /
        highLogTwoInterval.upper := by
    unfold YoshidaSineMomentEnclosures.piFineInterval highLogTwoInterval
    positivity
  nlinarith [sq_pos_of_pos hyn, sq_nonneg u]

private def highProfileInterval (n : ℕ) (u : ℚ) : RatInterval :=
  pure u / highProfileDenInterval n u

private theorem highProfileInterval_contains
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    (highProfileInterval n u).Contains
      (reciprocalRealPart (yoshidaY n) (u : ℝ)) := by
  unfold highProfileInterval reciprocalRealPart
  exact contains_div_of_pos (highProfileDenInterval_lower_pos hn u)
    (contains_pure u) (highProfileDenInterval_contains hn u)

private def highProfileDerivInterval (n : ℕ) (u : ℚ) : RatInterval :=
  (highYSqInterval n - pure (u ^ 2)) /
    highPositivePow (highProfileDenInterval n u) 2

private theorem highProfileDerivInterval_contains
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    (highProfileDerivInterval n u).Contains
      (reciprocalRealPartDeriv (yoshidaY n) (u : ℝ)) := by
  have hden := highProfileDenInterval_contains hn u
  have hdenPow := highPositivePow_contains
    (highProfileDenInterval_lower_pos hn u).le hden 2
  have huSq : (pure (u ^ 2)).Contains ((u : ℝ) ^ 2) := by
    norm_num [Contains, RatInterval.pure]
  have hnum := contains_sub (highYSqInterval_contains hn) huSq
  unfold highProfileDerivInterval reciprocalRealPartDeriv
  exact contains_div_of_pos (by
    unfold highPositivePow
    exact pow_pos (highProfileDenInterval_lower_pos hn u) 2)
    hnum hdenPow

private def highProfileThirdInterval (n : ℕ) (u : ℚ) : RatInterval :=
  (pure (-6) *
      (pure (u ^ 4) - pure (6 * u ^ 2) * highYSqInterval n +
        highPositiveSquare (highYSqInterval n))) /
    highPositivePow (highProfileDenInterval n u) 4

private theorem highProfileThirdInterval_contains
    {n : ℕ} (hn : n ≠ 0) (u : ℚ) :
    (highProfileThirdInterval n u).Contains
      (diagonalHighProfileThirdDeriv
        (yoshidaY n) ((u : ℝ) - 1 / 4)) := by
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

private def quarterVerticalDigammaRationalMainInterval
    (n : ℕ) : RatInterval :=
  -highProfileInterval n (1 / 4) / pure 2 +
      highProfileDerivInterval n (1 / 4) / pure 12 -
    highProfileThirdInterval n (1 / 4) / pure 720

private theorem quarterVerticalDigammaRationalMainInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (quarterVerticalDigammaRationalMainInterval n).Contains
      (-diagonalHighProfile (yoshidaY n) 0 / 2 +
        diagonalHighProfileDeriv (yoshidaY n) 0 / 12 -
        diagonalHighProfileThirdDeriv (yoshidaY n) 0 / 720) := by
  have hp := highProfileInterval_contains hn (1 / 4)
  have hd := highProfileDerivInterval_contains hn (1 / 4)
  have ht := highProfileThirdInterval_contains hn (1 / 4)
  have htwo : (pure 2).Contains (2 : ℝ) := contains_pure 2
  have htwelve : (pure 12).Contains (12 : ℝ) := contains_pure 12
  have hsevenTwenty : (pure 720).Contains (720 : ℝ) := contains_pure 720
  have hcombine := contains_sub
    (contains_add
      (contains_div_of_pos (by norm_num [RatInterval.pure])
        (contains_neg hp) htwo)
      (contains_div_of_pos (by norm_num [RatInterval.pure]) hd htwelve))
    (contains_div_of_pos (by norm_num [RatInterval.pure]) ht hsevenTwenty)
  unfold quarterVerticalDigammaRationalMainInterval
    diagonalHighProfile diagonalHighProfileDeriv
  convert hcombine using 1
  all_goals norm_num

private def highDigammaRadius (n : ℕ) : ℚ :=
  4 / (3 * (highYInterval n).lower ^ 5)

private theorem highDigammaRadius_bound
    {n : ℕ} (hn : n ≠ 0) :
    4 / (3 * yoshidaY n ^ 5) ≤ (highDigammaRadius n : ℝ) := by
  have hy := highYInterval_contains n
  have hylQ := highYInterval_lower_pos hn
  have hyl : (0 : ℝ) < ((highYInterval n).lower : ℚ) := by
    exact_mod_cast hylQ
  have hden :
      3 * ((highYInterval n).lower : ℝ) ^ 5 ≤
        3 * yoshidaY n ^ 5 := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hyl.le hy.1 5) (by norm_num)
  unfold highDigammaRadius
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden

/-- Symmetric rational enclosure for the corrected-trapezoid error in the
quarter-line digamma high main term. -/
def quarterVerticalDigammaHighMainErrorInterval (n : ℕ) : RatInterval :=
  ⟨-highDigammaRadius n, highDigammaRadius n⟩

theorem quarterVerticalDigammaHighMainErrorInterval_contains
    {n : ℕ} (hn : n ≠ 0) :
    (quarterVerticalDigammaHighMainErrorInterval n).Contains
      ((Complex.digamma ((1 / 4 : ℝ) + yoshidaY n * Complex.I)).re -
        diagonalDigammaMain (yoshidaY n)) := by
  have hy : 0 < yoshidaY n := by
    exact (show (0 : ℝ) < (highYInterval n).lower by
      exact_mod_cast highYInterval_lower_pos hn).trans_le
        (highYInterval_contains n).1
  have hraw := digamma_quarter_vertical_re_sub_highMain_abs_le hy
  have hradius := highDigammaRadius_bound hn
  have h := hraw.trans hradius
  rw [abs_le] at h
  unfold quarterVerticalDigammaHighMainErrorInterval Contains
  norm_num only [Rat.cast_neg]
  exact h

/-- Exact rational target for the nonlogarithmic quarter-line digamma
residual

`Re ψ(1/4 + i yₙ) - log(1/16 + yₙ²)/2`.

The omitted logarithmic primitive can be enclosed independently and added by
ordinary rational interval arithmetic. -/
def quarterVerticalDigammaLogResidualTarget (n : ℕ) : RatInterval :=
  quarterVerticalDigammaRationalMainInterval n +
    quarterVerticalDigammaHighMainErrorInterval n

theorem quarterVerticalDigammaLogResidualTarget_contains
    {n : ℕ} (hn : n ≠ 0) :
    (quarterVerticalDigammaLogResidualTarget n).Contains
      ((Complex.digamma ((1 / 4 : ℝ) + yoshidaY n * Complex.I)).re -
        Real.log ((1 / 16 : ℝ) + yoshidaY n ^ 2) / 2) := by
  have hm := quarterVerticalDigammaRationalMainInterval_contains hn
  have he := quarterVerticalDigammaHighMainErrorInterval_contains hn
  have hsum := contains_add hm he
  unfold quarterVerticalDigammaLogResidualTarget
  unfold diagonalDigammaMain at hsum
  convert hsum using 1
  ring

/-! ## Structural high-band width bounds -/

private theorem highAbsBound_mono
    {I : RatInterval} {B C : ℚ} (hI : I.AbsBound B) (hBC : B ≤ C) :
    I.AbsBound C := by
  unfold AbsBound at hI ⊢
  exact ⟨(neg_le_neg hBC).trans hI.1, hI.2.trans hBC⟩

private theorem highValid_neg {I : RatInterval} (hI : I.Valid) :
    (-I).Valid := by
  change -I.upper ≤ -I.lower
  exact neg_le_neg hI

private theorem highWidth_neg (I : RatInterval) : width (-I) = width I := by
  change -I.lower - -I.upper = I.upper - I.lower
  ring

private theorem highWidth_div_pure_pos
    {I : RatInterval} (hI : I.Valid) {q : ℚ} (hq : 0 < q) :
    width (I / pure q) = q⁻¹ * width I := by
  change width (I * (pure q)⁻¹) = q⁻¹ * width I
  rw [show (pure q)⁻¹ = pure q⁻¹ by rfl,
    width_mul_pure q⁻¹ hI, abs_of_pos (inv_pos.mpr hq)]

private theorem highQuarterDenInterval_lower_pos
    {n : ℕ} (hn : 1 ≤ n) :
    0 < (highProfileDenInterval n (1 / 4)).lower := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (show (0 : ℚ) < 16 * n ^ 2 by positivity).trans_le
    (highQuarterDenInterval_lower_ge n)

private theorem highQuarterProfileInterval_valid
    {n : ℕ} (hn : 1 ≤ n) :
    (highProfileInterval n (1 / 4)).Valid := by
  exact valid_div_of_pos (valid_pure _) (highQuarterDenInterval_valid n)
    (highQuarterDenInterval_lower_pos hn)

private theorem highQuarterProfileInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (highProfileInterval n (1 / 4)) ≤
      1 / (100000000000000 * (n : ℚ) ^ 2) := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  let m : ℚ := 16 * (n : ℚ) ^ 2
  have hm : 0 < m := by dsimp only [m]; positivity
  have hraw := width_div_le_of_lower
    (I := pure (1 / 4 : ℚ))
    (J := highProfileDenInterval n (1 / 4))
    (B := (1 / 4 : ℚ)) (m := m)
    (valid_pure _) (highQuarterDenInterval_valid n)
    (absBound_pure (by norm_num)) (by norm_num) hm
    (by simpa only [m] using highQuarterDenInterval_lower_ge n)
  rw [width_pure, mul_zero, zero_add] at hraw
  calc
    width (highProfileInterval n (1 / 4)) ≤
        (1 / 4 : ℚ) *
          (width (highProfileDenInterval n (1 / 4)) / (m * m)) := hraw
    _ ≤ (1 / 4 : ℚ) *
          (((n : ℚ) ^ 2 / 1500000000000) / (m * m)) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (highQuarterDenInterval_width_le n)
          (mul_nonneg hm.le hm.le)) (by norm_num)
    _ ≤ 1 / (100000000000000 * (n : ℚ) ^ 2) := by
      dsimp only [m]
      field_simp
      nlinarith [sq_pos_of_pos hnQ]

private theorem highQuarterDerivNumerator_valid (n : ℕ) :
    (highYSqInterval n - pure ((1 / 4 : ℚ) ^ 2)).Valid :=
  valid_sub (highYSqInterval_valid n) (valid_pure _)

private theorem highQuarterDerivNumerator_absBound
    {n : ℕ} (hn : 1 ≤ n) :
    (highYSqInterval n - pure ((1 / 4 : ℚ) ^ 2)).AbsBound
      (26 * (n : ℚ) ^ 2) := by
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  unfold AbsBound
  change
    -(26 * (n : ℚ) ^ 2) ≤
          (highYSqInterval n).lower - (1 / 4 : ℚ) ^ 2 ∧
      (highYSqInterval n).upper - (1 / 4 : ℚ) ^ 2 ≤
          26 * (n : ℚ) ^ 2
  constructor
  · nlinarith [highYSqInterval_lower_ge n, sq_nonneg ((n : ℚ) - 1)]
  · nlinarith [highYSqInterval_upper_le n]

private theorem highQuarterDerivNumerator_width_le (n : ℕ) :
    width (highYSqInterval n - pure ((1 / 4 : ℚ) ^ 2)) ≤
      (n : ℚ) ^ 2 / 1500000000000 := by
  rw [width_sub, width_pure, add_zero]
  exact highYSqInterval_width_le n

private theorem highQuarterDenSquare_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (highPositivePow (highProfileDenInterval n (1 / 4)) 2) ≤
      (n : ℚ) ^ 4 / 28000000000 := by
  calc
    width (highPositivePow (highProfileDenInterval n (1 / 4)) 2) ≤
        (2 : ℚ) * ((26 : ℚ) * n ^ 2) ^ (2 - 1) *
          ((n : ℚ) ^ 2 / 1500000000000) :=
      highQuarterDenPow_width_le hn
    _ ≤ (n : ℚ) ^ 4 / 28000000000 := by
      have hn0 : (0 : ℚ) ≤ n := by positivity
      ring_nf
      nlinarith [sq_nonneg ((n : ℚ) ^ 2)]

private theorem highQuarterProfileDerivInterval_valid
    {n : ℕ} (hn : 1 ≤ n) :
    (highProfileDerivInterval n (1 / 4)).Valid := by
  exact valid_div_of_pos (highQuarterDerivNumerator_valid n)
    highQuarterDenPow_valid (by
      have hm := highQuarterDenInterval_lower_pos hn
      unfold highPositivePow
      positivity)

private theorem highQuarterProfileDerivInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (highProfileDerivInterval n (1 / 4)) ≤
      1 / (1000000000000 * (n : ℚ) ^ 2) := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  let m : ℚ := 256 * (n : ℚ) ^ 4
  have hm : 0 < m := by dsimp only [m]; positivity
  have hmLower : m ≤
      (highPositivePow (highProfileDenInterval n (1 / 4)) 2).lower := by
    have h := highQuarterDenPow_lower_ge n 2
    dsimp only [m]
    norm_num at h ⊢
    nlinarith
  have hraw := width_div_le_of_lower
    (I := highYSqInterval n - pure ((1 / 4 : ℚ) ^ 2))
    (J := highPositivePow (highProfileDenInterval n (1 / 4)) 2)
    (B := 26 * (n : ℚ) ^ 2) (m := m)
    (highQuarterDerivNumerator_valid n) highQuarterDenPow_valid
    (highQuarterDerivNumerator_absBound hn) (by positivity) hm hmLower
  calc
    width (highProfileDerivInterval n (1 / 4)) ≤
        m⁻¹ * width (highYSqInterval n - pure ((1 / 4 : ℚ) ^ 2)) +
          (26 * (n : ℚ) ^ 2) *
            (width (highPositivePow
              (highProfileDenInterval n (1 / 4)) 2) / (m * m)) := hraw
    _ ≤ m⁻¹ * ((n : ℚ) ^ 2 / 1500000000000) +
          (26 * (n : ℚ) ^ 2) *
            (((n : ℚ) ^ 4 / 28000000000) / (m * m)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (highQuarterDerivNumerator_width_le n)
          (inv_nonneg.mpr hm.le))
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (highQuarterDenSquare_width_le hn)
            (mul_nonneg hm.le hm.le)) (by positivity))
    _ ≤ 1 / (1000000000000 * (n : ℚ) ^ 2) := by
      dsimp only [m]
      field_simp
      nlinarith [sq_pos_of_pos hnQ]

private theorem highYSqInterval_absBound (n : ℕ) :
    (highYSqInterval n).AbsBound (25 * (n : ℚ) ^ 2) := by
  unfold AbsBound
  constructor
  · exact (neg_nonpos.mpr (by positivity)).trans (by
      unfold highYSqInterval highPositiveSquare
      positivity)
  · exact highYSqInterval_upper_le n

private theorem highYSqSquare_valid (n : ℕ) :
    (highPositiveSquare (highYSqInterval n)).Valid := by
  change (highPositivePow (highYSqInterval n) 2).Valid
  exact highPositivePow_valid (by
      unfold highYSqInterval highPositiveSquare
      positivity)
    (highYSqInterval_valid n) 2

private theorem highYSqSquare_absBound (n : ℕ) :
    (highPositiveSquare (highYSqInterval n)).AbsBound
      (625 * (n : ℚ) ^ 4) := by
  unfold AbsBound highPositiveSquare
  constructor
  · exact (neg_nonpos.mpr (by positivity)).trans (sq_nonneg _)
  · have h := pow_le_pow_left₀
      (show (0 : ℚ) ≤ (highYSqInterval n).upper by
        exact (show (0 : ℚ) ≤ (highYSqInterval n).lower by
          unfold highYSqInterval highPositiveSquare
          positivity).trans (highYSqInterval_valid n))
      (highYSqInterval_upper_le n) 2
    nlinarith

private theorem highYSqSquare_width_le (n : ℕ) :
    width (highPositiveSquare (highYSqInterval n)) ≤
      (n : ℚ) ^ 4 / 30000000000 := by
  have h := highPositivePow_width_le
    (show (0 : ℚ) ≤ (highYSqInterval n).lower by
      unfold highYSqInterval highPositiveSquare
      positivity)
    (highYSqInterval_valid n) (highYSqInterval_upper_le n)
    (highYSqInterval_width_le n) 2
  change width (highPositivePow (highYSqInterval n) 2) ≤
    (n : ℚ) ^ 4 / 30000000000
  calc
    width (highPositivePow (highYSqInterval n) 2) ≤
        (2 : ℚ) * ((25 : ℚ) * n ^ 2) ^ (2 - 1) *
          ((n : ℚ) ^ 2 / 1500000000000) := h
    _ = (n : ℚ) ^ 4 / 30000000000 := by ring

private def highQuarterThirdPolyInterval (n : ℕ) : RatInterval :=
  pure ((1 / 4 : ℚ) ^ 4) -
      pure (6 * (1 / 4 : ℚ) ^ 2) * highYSqInterval n +
    highPositiveSquare (highYSqInterval n)

private theorem highQuarterThirdPoly_valid (n : ℕ) :
    (highQuarterThirdPolyInterval n).Valid := by
  exact valid_add
    (valid_sub (valid_pure _)
      (valid_mul (valid_pure _) (highYSqInterval_valid n)))
    (highYSqSquare_valid n)

private theorem highQuarterThirdPoly_absBound
    {n : ℕ} (hn : 1 ≤ n) :
    (highQuarterThirdPolyInterval n).AbsBound
      (636 * (n : ℚ) ^ 4) := by
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hconst : (pure ((1 / 4 : ℚ) ^ 4)).AbsBound 1 :=
    absBound_pure (by norm_num)
  have hcoeff : (pure (6 * (1 / 4 : ℚ) ^ 2)).AbsBound (3 / 8) :=
    absBound_pure (by norm_num)
  have hprod := absBound_mul (valid_pure _)
    (highYSqInterval_valid n) hcoeff (highYSqInterval_absBound n)
    (by norm_num) (by positivity)
  have hsum := absBound_add (absBound_sub hconst hprod)
    (highYSqSquare_absBound n)
  unfold highQuarterThirdPolyInterval
  apply highAbsBound_mono hsum
  nlinarith [sq_nonneg ((n : ℚ) - 1), sq_nonneg ((n : ℚ) ^ 2 - 1)]

private theorem highQuarterThirdPoly_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (highQuarterThirdPolyInterval n) ≤
      (n : ℚ) ^ 4 / 29000000000 := by
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  rw [highQuarterThirdPolyInterval, width_add, width_sub, width_pure,
    zero_add, width_pure_mul _ (highYSqInterval_valid n)]
  norm_num only [abs_of_nonneg (show (0 : ℚ) ≤ 6 * (1 / 4) ^ 2 by
    norm_num)]
  calc
    (3 / 8 : ℚ) * width (highYSqInterval n) +
        width (highPositiveSquare (highYSqInterval n)) ≤
      (3 / 8 : ℚ) * ((n : ℚ) ^ 2 / 1500000000000) +
        (n : ℚ) ^ 4 / 30000000000 :=
      add_le_add
        (mul_le_mul_of_nonneg_left (highYSqInterval_width_le n)
          (by norm_num))
        (highYSqSquare_width_le n)
    _ ≤ (n : ℚ) ^ 4 / 29000000000 := by
      have hn2 : (n : ℚ) ^ 2 ≤ (n : ℚ) ^ 4 := by
        nlinarith [sq_nonneg ((n : ℚ) ^ 2 - 1)]
      nlinarith

private theorem highQuarterThirdNumerator_valid (n : ℕ) :
    (pure (-6) * highQuarterThirdPolyInterval n).Valid :=
  valid_mul (valid_pure _) (highQuarterThirdPoly_valid n)

private theorem highQuarterThirdNumerator_absBound
    {n : ℕ} (hn : 1 ≤ n) :
    (pure (-6) * highQuarterThirdPolyInterval n).AbsBound
      (4000 * (n : ℚ) ^ 4) := by
  have hpure : (pure (-6 : ℚ)).AbsBound 6 :=
    absBound_pure (by norm_num)
  have h := absBound_mul (valid_pure _)
    (highQuarterThirdPoly_valid n) hpure
    (highQuarterThirdPoly_absBound hn) (by norm_num) (by positivity)
  apply highAbsBound_mono h
  have hn4 : (0 : ℚ) ≤ (n : ℚ) ^ 4 := by positivity
  nlinarith

private theorem highQuarterThirdNumerator_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (pure (-6) * highQuarterThirdPolyInterval n) ≤
      (n : ℚ) ^ 4 / 4000000000 := by
  rw [width_pure_mul _ (highQuarterThirdPoly_valid n)]
  norm_num only [abs_of_nonpos (by norm_num : (-6 : ℚ) ≤ 0), neg_neg]
  calc
    (6 : ℚ) * width (highQuarterThirdPolyInterval n) ≤
        6 * ((n : ℚ) ^ 4 / 29000000000) :=
      mul_le_mul_of_nonneg_left (highQuarterThirdPoly_width_le hn) (by norm_num)
    _ ≤ (n : ℚ) ^ 4 / 4000000000 := by
      have hn4 : (0 : ℚ) ≤ (n : ℚ) ^ 4 := by positivity
      nlinarith

private theorem highQuarterDenFourth_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (highPositivePow (highProfileDenInterval n (1 / 4)) 4) ≤
      (n : ℚ) ^ 8 / 20000000 := by
  calc
    width (highPositivePow (highProfileDenInterval n (1 / 4)) 4) ≤
        (4 : ℚ) * ((26 : ℚ) * n ^ 2) ^ (4 - 1) *
          ((n : ℚ) ^ 2 / 1500000000000) :=
      highQuarterDenPow_width_le hn
    _ ≤ (n : ℚ) ^ 8 / 20000000 := by
      have hn0 : (0 : ℚ) ≤ n := by positivity
      ring_nf
      nlinarith [pow_nonneg hn0 8]

private theorem highQuarterProfileThirdInterval_valid
    {n : ℕ} (hn : 1 ≤ n) :
    (highProfileThirdInterval n (1 / 4)).Valid := by
  change (pure (-6) * highQuarterThirdPolyInterval n /
    highPositivePow (highProfileDenInterval n (1 / 4)) 4).Valid
  exact valid_div_of_pos (highQuarterThirdNumerator_valid n)
    highQuarterDenPow_valid (by
      have hm := highQuarterDenInterval_lower_pos hn
      unfold highPositivePow
      positivity)

private theorem highQuarterProfileThirdInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (highProfileThirdInterval n (1 / 4)) ≤
      1 / (1000000000000 * (n : ℚ) ^ 4) := by
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
  let m : ℚ := 65536 * (n : ℚ) ^ 8
  have hm : 0 < m := by dsimp only [m]; positivity
  have hmLower : m ≤
      (highPositivePow (highProfileDenInterval n (1 / 4)) 4).lower := by
    have h := highQuarterDenPow_lower_ge n 4
    dsimp only [m]
    norm_num at h ⊢
    nlinarith
  have hraw := width_div_le_of_lower
    (I := pure (-6) * highQuarterThirdPolyInterval n)
    (J := highPositivePow (highProfileDenInterval n (1 / 4)) 4)
    (B := 4000 * (n : ℚ) ^ 4) (m := m)
    (highQuarterThirdNumerator_valid n) highQuarterDenPow_valid
    (highQuarterThirdNumerator_absBound hn) (by positivity) hm hmLower
  change width (pure (-6) * highQuarterThirdPolyInterval n /
    highPositivePow (highProfileDenInterval n (1 / 4)) 4) ≤ _
  calc
    width (pure (-6) * highQuarterThirdPolyInterval n /
        highPositivePow (highProfileDenInterval n (1 / 4)) 4) ≤
      m⁻¹ * width (pure (-6) * highQuarterThirdPolyInterval n) +
        (4000 * (n : ℚ) ^ 4) *
          (width (highPositivePow
            (highProfileDenInterval n (1 / 4)) 4) / (m * m)) := hraw
    _ ≤ m⁻¹ * ((n : ℚ) ^ 4 / 4000000000) +
        (4000 * (n : ℚ) ^ 4) *
          (((n : ℚ) ^ 8 / 20000000) / (m * m)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (highQuarterThirdNumerator_width_le hn)
          (inv_nonneg.mpr hm.le))
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (highQuarterDenFourth_width_le hn)
            (mul_nonneg hm.le hm.le)) (by positivity))
    _ ≤ 1 / (1000000000000 * (n : ℚ) ^ 4) := by
      dsimp only [m]
      field_simp
      nlinarith [sq_pos_of_pos hnQ]

private theorem quarterVerticalDigammaRationalMainInterval_valid
    {n : ℕ} (hn : 1 ≤ n) :
    (quarterVerticalDigammaRationalMainInterval n).Valid := by
  exact valid_sub
    (valid_add
      (valid_div_of_pos
        (highValid_neg (highQuarterProfileInterval_valid hn))
        (valid_pure 2) (by norm_num [RatInterval.pure]))
      (valid_div_of_pos (highQuarterProfileDerivInterval_valid hn)
        (valid_pure 12) (by norm_num [RatInterval.pure])))
    (valid_div_of_pos (highQuarterProfileThirdInterval_valid hn)
      (valid_pure 720) (by norm_num [RatInterval.pure]))

private theorem quarterVerticalDigammaRationalMainInterval_width_le
    {n : ℕ} (hn : 1 ≤ n) :
    width (quarterVerticalDigammaRationalMainInterval n) ≤
      (1 / 1000000000000 : ℚ) := by
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hpValid := highQuarterProfileInterval_valid hn
  have hdValid := highQuarterProfileDerivInterval_valid hn
  have htValid := highQuarterProfileThirdInterval_valid hn
  have hp :
      width (-highProfileInterval n (1 / 4) / pure 2) =
        (1 / 2 : ℚ) * width (highProfileInterval n (1 / 4)) := by
    rw [highWidth_div_pure_pos (highValid_neg hpValid) (by norm_num),
      highWidth_neg]
    norm_num
  have hd :
      width (highProfileDerivInterval n (1 / 4) / pure 12) =
        (1 / 12 : ℚ) *
          width (highProfileDerivInterval n (1 / 4)) := by
    rw [highWidth_div_pure_pos hdValid (by norm_num)]
    norm_num
  have ht :
      width (highProfileThirdInterval n (1 / 4) / pure 720) =
        (1 / 720 : ℚ) *
          width (highProfileThirdInterval n (1 / 4)) := by
    rw [highWidth_div_pure_pos htValid (by norm_num)]
    norm_num
  rw [quarterVerticalDigammaRationalMainInterval, width_sub, width_add,
    hp, hd, ht]
  calc
    (1 / 2 : ℚ) * width (highProfileInterval n (1 / 4)) +
          (1 / 12 : ℚ) * width (highProfileDerivInterval n (1 / 4)) +
        (1 / 720 : ℚ) * width (highProfileThirdInterval n (1 / 4)) ≤
      (1 / 2 : ℚ) *
          (1 / (100000000000000 * (n : ℚ) ^ 2)) +
        (1 / 12 : ℚ) *
          (1 / (1000000000000 * (n : ℚ) ^ 2)) +
        (1 / 720 : ℚ) *
          (1 / (1000000000000 * (n : ℚ) ^ 4)) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (highQuarterProfileInterval_width_le hn)
            (by norm_num))
          (mul_le_mul_of_nonneg_left
            (highQuarterProfileDerivInterval_width_le hn) (by norm_num)))
        (mul_le_mul_of_nonneg_left
          (highQuarterProfileThirdInterval_width_le hn) (by norm_num))
    _ ≤ (1 / 1000000000000 : ℚ) := by
      have hn2 : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by
        nlinarith [sq_nonneg ((n : ℚ) - 1)]
      have hn4 : (1 : ℚ) ≤ (n : ℚ) ^ 4 := by
        nlinarith [sq_nonneg ((n : ℚ) ^ 2 - 1)]
      have hpDen : (100000000000000 : ℚ) ≤
          100000000000000 * (n : ℚ) ^ 2 := by
        nlinarith
      have hdDen : (1000000000000 : ℚ) ≤
          1000000000000 * (n : ℚ) ^ 2 := by
        nlinarith
      have htDen : (1000000000000 : ℚ) ≤
          1000000000000 * (n : ℚ) ^ 4 := by
        nlinarith
      calc
        (1 / 2 : ℚ) *
              (1 / (100000000000000 * (n : ℚ) ^ 2)) +
            (1 / 12 : ℚ) *
              (1 / (1000000000000 * (n : ℚ) ^ 2)) +
            (1 / 720 : ℚ) *
              (1 / (1000000000000 * (n : ℚ) ^ 4)) ≤
          (1 / 2 : ℚ) * (1 / 100000000000000) +
            (1 / 12 : ℚ) * (1 / 1000000000000) +
            (1 / 720 : ℚ) * (1 / 1000000000000) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_left
                (one_div_le_one_div_of_le (by norm_num) hpDen) (by norm_num))
              (mul_le_mul_of_nonneg_left
                (one_div_le_one_div_of_le (by norm_num) hdDen) (by norm_num)))
            (mul_le_mul_of_nonneg_left
              (one_div_le_one_div_of_le (by norm_num) htDen) (by norm_num))
        _ ≤ (1 / 1000000000000 : ℚ) := by norm_num

private theorem highYInterval_lower_ge_seventySeven
    {n : ℕ} (hn17 : 17 ≤ n) :
    (77 : ℚ) ≤ (highYInterval n).lower := by
  have hnQ : (17 : ℚ) ≤ n := by exact_mod_cast hn17
  have hcoefPos : (0 : ℚ) ≤
      YoshidaSineMomentEnclosures.piFineInterval.lower /
        highLogTwoInterval.upper := by
    norm_num [YoshidaSineMomentEnclosures.piFineInterval,
      highLogTwoInterval]
  have hbase : (77 : ℚ) ≤
      (YoshidaSineMomentEnclosures.piFineInterval.lower /
        highLogTwoInterval.upper) * 17 := by
    norm_num [YoshidaSineMomentEnclosures.piFineInterval,
      highLogTwoInterval]
  unfold highYInterval
  calc
    (77 : ℚ) ≤
        (YoshidaSineMomentEnclosures.piFineInterval.lower /
          highLogTwoInterval.upper) * 17 := hbase
    _ ≤ (YoshidaSineMomentEnclosures.piFineInterval.lower /
          highLogTwoInterval.upper) * n :=
      mul_le_mul_of_nonneg_left hnQ hcoefPos
    _ = YoshidaSineMomentEnclosures.piFineInterval.lower * n /
        highLogTwoInterval.upper := by ring

private theorem quarterVerticalDigammaHighMainErrorInterval_width_le
    {n : ℕ} (hn17 : 17 ≤ n) :
    width (quarterVerticalDigammaHighMainErrorInterval n) ≤
      (99 / 100000000000 : ℚ) := by
  have hy := highYInterval_lower_ge_seventySeven hn17
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 77) hy 5
  have hden : (3 : ℚ) * 77 ^ 5 ≤
      3 * (highYInterval n).lower ^ 5 :=
    mul_le_mul_of_nonneg_left hpow (by norm_num)
  have hdiv :
      (8 : ℚ) / (3 * (highYInterval n).lower ^ 5) ≤
        8 / (3 * 77 ^ 5) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden
  unfold quarterVerticalDigammaHighMainErrorInterval highDigammaRadius width
  calc
    4 / (3 * (highYInterval n).lower ^ 5) -
        -(4 / (3 * (highYInterval n).lower ^ 5)) =
      8 / (3 * (highYInterval n).lower ^ 5) := by ring
    _ ≤ 8 / (3 * 77 ^ 5) := hdiv
    _ ≤ (99 / 100000000000 : ℚ) := by norm_num

/-- Exact kernel-checked width certificate for every positive canonical mode
from `17` through `200`. -/
theorem quarterVerticalDigammaLogResidualTarget_width_le
    {n : ℕ} (hn17 : 17 ≤ n) (_hn200 : n ≤ 200) :
    width (quarterVerticalDigammaLogResidualTarget n) ≤
      (1 / 1000000000 : ℚ) := by
  rw [quarterVerticalDigammaLogResidualTarget, width_add]
  calc
    width (quarterVerticalDigammaRationalMainInterval n) +
        width (quarterVerticalDigammaHighMainErrorInterval n) ≤
      (1 / 1000000000000 : ℚ) + 99 / 100000000000 :=
      add_le_add
        (quarterVerticalDigammaRationalMainInterval_width_le (by omega))
        (quarterVerticalDigammaHighMainErrorInterval_width_le hn17)
    _ ≤ (1 / 1000000000 : ℚ) := by norm_num

/-- Mode `16` is wider than `10⁻⁹`, so `17` is the sharp cutoff for
this direct rational residual enclosure family. -/
theorem quarterVerticalDigammaLogResidualTarget_16_width_gt :
    (1 / 1000000000 : ℚ) <
      width (quarterVerticalDigammaLogResidualTarget 16) := by
  have hyPos : (0 : ℚ) < (highYInterval 16).lower :=
    highYInterval_lower_pos (by norm_num)
  have hyUpper : (highYInterval 16).lower < (73 : ℚ) := by
    norm_num [highYInterval, YoshidaSineMomentEnclosures.piFineInterval,
      highLogTwoInterval]
  have hpow : (highYInterval 16).lower ^ 5 < (73 : ℚ) ^ 5 :=
    pow_lt_pow_left₀ hyUpper hyPos.le (by norm_num)
  have hden :
      3 * (highYInterval 16).lower ^ 5 < (3 : ℚ) * 73 ^ 5 :=
    mul_lt_mul_of_pos_left hpow (by norm_num)
  have hdiv :
      (8 : ℚ) / (3 * 73 ^ 5) <
        8 / (3 * (highYInterval 16).lower ^ 5) := by
    exact (div_lt_div_iff_of_pos_left (by norm_num)
      (by positivity) (by positivity)).2 hden
  have herr :
      (1 / 1000000000 : ℚ) <
        width (quarterVerticalDigammaHighMainErrorInterval 16) := by
    unfold quarterVerticalDigammaHighMainErrorInterval highDigammaRadius width
    calc
      (1 / 1000000000 : ℚ) < 8 / (3 * 73 ^ 5) := by norm_num
      _ < 8 / (3 * (highYInterval 16).lower ^ 5) := hdiv
      _ = 4 / (3 * (highYInterval 16).lower ^ 5) -
          -(4 / (3 * (highYInterval 16).lower ^ 5)) := by ring
  have hmain : 0 ≤
      width (quarterVerticalDigammaRationalMainInterval 16) :=
    width_nonneg (quarterVerticalDigammaRationalMainInterval_valid
      (by norm_num))
  rw [quarterVerticalDigammaLogResidualTarget, width_add]
  linarith

/-- Complete containment and width obligation for the canonical high band. -/
def YoshidaQuarterVerticalDigammaHighResidualEnclosures : Prop :=
  ∀ n, 17 ≤ n → n ≤ 200 →
    (quarterVerticalDigammaLogResidualTarget n).Contains
        ((Complex.digamma ((1 / 4 : ℝ) + yoshidaY n * Complex.I)).re -
          Real.log ((1 / 16 : ℝ) + yoshidaY n ^ 2) / 2) ∧
      width (quarterVerticalDigammaLogResidualTarget n) ≤
        (1 / 1000000000 : ℚ)

theorem yoshidaQuarterVerticalDigammaHighResidualEnclosures :
    YoshidaQuarterVerticalDigammaHighResidualEnclosures := by
  intro n hn17 hn200
  exact ⟨quarterVerticalDigammaLogResidualTarget_contains (by omega),
    quarterVerticalDigammaLogResidualTarget_width_le hn17 hn200⟩

end

end ArithmeticHodge.Analysis.YoshidaQuarterVerticalDigammaHighEnclosures
