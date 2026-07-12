import ArithmeticHodge.Analysis.YoshidaSineSeriesTail
import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaOddMomentTargets

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures

open RatInterval
open YoshidaConstantBounds
open YoshidaMomentSeries
open YoshidaOddGramPrefix
open YoshidaOddMomentTargets
open YoshidaRenormalizedGeometricKernel
open YoshidaSineSeriesTail

noncomputable section

/-!
# Certified enclosures for Yoshida's sine moments

Fine rational enclosures for the constants in the explicit Cauchy-series
formula, kernel-computable finite heads, and the certified production tail
combine to discharge all ten sine-moment target boxes.
-/

def sqrtTwoInterval : RatInterval :=
  ⟨1414213562373095 / 1000000000000000,
    1414213562373096 / 1000000000000000⟩

def piFineInterval : RatInterval :=
  ⟨314159265358979323846 / 100000000000000000000,
    314159265358979323847 / 100000000000000000000⟩

def logTwoFineInterval : RatInterval :=
  ⟨69314718055 / 100000000000,
    69314718057 / 100000000000⟩

theorem sqrtTwoInterval_contains :
    sqrtTwoInterval.Contains (Real.sqrt 2) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg 2
  constructor <;> norm_num [sqrtTwoInterval, Contains] <;> nlinarith

theorem piFineInterval_contains : piFineInterval.Contains Real.pi := by
  constructor
  · have h := Real.pi_gt_d20
    norm_num [piFineInterval, Contains] at h ⊢
    exact h.le
  · have h := Real.pi_lt_d20
    norm_num [piFineInterval, Contains] at h ⊢
    exact h.le

theorem logTwoFineInterval_contains :
    logTwoFineInterval.Contains yoshidaLength := by
  constructor
  · have h := strict_log_two_fine_bounds.1
    norm_num [logTwoFineInterval, Contains, yoshidaLength] at h ⊢
    exact h.le
  · have h := strict_log_two_fine_bounds.2
    norm_num [logTwoFineInterval, Contains, yoshidaLength] at h ⊢
    exact h.le

def yoshidaY (n : ℕ) : ℝ := Real.pi * n / yoshidaLength

def yoshidaYInterval (n : ℕ) : RatInterval :=
  ⟨piFineInterval.lower * n / logTwoFineInterval.upper,
    piFineInterval.upper * n / logTwoFineInterval.lower⟩

theorem yoshidaYInterval_contains (n : ℕ) :
    (yoshidaYInterval n).Contains (yoshidaY n) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnum0 : 0 ≤ Real.pi * (n : ℝ) := mul_nonneg Real.pi_pos.le hn0
  have hnumLo : (piFineInterval.lower : ℝ) * (n : ℝ) ≤
      Real.pi * (n : ℝ) :=
    mul_le_mul_of_nonneg_right piFineInterval_contains.1 hn0
  have hnumHi : Real.pi * (n : ℝ) ≤
      (piFineInterval.upper : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right piFineInterval_contains.2 hn0
  have hlogLowerPos : (0 : ℝ) < logTwoFineInterval.lower := by
    norm_num [logTwoFineInterval]
  have hlogUpper : yoshidaLength ≤ (logTwoFineInterval.upper : ℝ) :=
    logTwoFineInterval_contains.2
  have hlogLower : (logTwoFineInterval.lower : ℝ) ≤ yoshidaLength :=
    logTwoFineInterval_contains.1
  constructor
  · change ((piFineInterval.lower * n / logTwoFineInterval.upper : ℚ) : ℝ) ≤
      Real.pi * (n : ℝ) / yoshidaLength
    norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    exact div_le_div₀ hnum0 hnumLo yoshidaLength_pos hlogUpper
  · change Real.pi * (n : ℝ) / yoshidaLength ≤
      ((piFineInterval.upper * n / logTwoFineInterval.lower : ℚ) : ℝ)
    norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast]
    exact div_le_div₀ (mul_nonneg (by
      exact_mod_cast (show (0 : ℚ) ≤ piFineInterval.upper by
        norm_num [piFineInterval])) hn0) hnumHi hlogLowerPos hlogLower

theorem yoshidaKappa_eq_two_mul_y (n : ℕ) :
    yoshidaKappa n = 2 * yoshidaY n := by
  rw [yoshidaKappa, yoshidaY]
  ring

/-- Squaring is monotone for intervals already known to be nonnegative. -/
def nonnegSquare (I : RatInterval) : RatInterval :=
  ⟨I.lower ^ 2, I.upper ^ 2⟩

theorem contains_nonnegSquare
    {I : RatInterval} {x : ℝ} (hI0 : 0 ≤ I.lower)
    (hx : I.Contains x) :
    (nonnegSquare I).Contains (x ^ 2) := by
  have hl0 : (0 : ℝ) ≤ I.lower := by exact_mod_cast hI0
  have hx0 : 0 ≤ x := hl0.trans hx.1
  constructor
  · norm_num [nonnegSquare, Contains]
    exact pow_le_pow_left₀ hl0 hx.1 2
  · norm_num [nonnegSquare, Contains]
    exact pow_le_pow_left₀ hx0 hx.2 2

def quarterShiftQ (k : ℕ) : ℚ := k + 1 / 4

def cauchyDenomInterval (n k : ℕ) : RatInterval :=
  pure (quarterShiftQ k ^ 2) + nonnegSquare (yoshidaYInterval n)

theorem quarterShiftQ_pos (k : ℕ) : 0 < quarterShiftQ k := by
  unfold quarterShiftQ
  positivity

theorem cauchyDenomInterval_lower_pos (n k : ℕ) :
    0 < (cauchyDenomInterval n k).lower := by
  change 0 < quarterShiftQ k ^ 2 + (yoshidaYInterval n).lower ^ 2
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (quarterShiftQ_pos k))
    (sq_nonneg _)

def scaledSineCauchyTerm (n k : ℕ) : ℝ :=
  yoshidaY n *
      (1 - (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) /
    (((k : ℝ) + 1 / 4) ^ 2 + yoshidaY n ^ 2)

theorem sineCauchyTerm_eq_scaled
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    sineCauchyTerm n k = scaledSineCauchyTerm n k := by
  have hy : yoshidaY n ≠ 0 := by
    rw [yoshidaY]
    exact div_ne_zero
      (mul_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hn))
      yoshidaLength_pos.ne'
  have hden : (((k : ℝ) + 1 / 4) ^ 2 + yoshidaY n ^ 2) ≠ 0 := by
    positivity
  rw [sineCauchyTerm, scaledSineCauchyTerm, yoshidaKappa_eq_two_mul_y,
    oddRate]
  field_simp [hden, hy]
  ring

def scaledSineCauchyTermInterval (n k : ℕ) : RatInterval :=
  yoshidaYInterval n *
      (pure 1 - sqrtTwoInterval⁻¹ / pure ((4 : ℚ) ^ k)) /
    cauchyDenomInterval n k

private theorem yoshidaYInterval_lower_nonneg (n : ℕ) :
    0 ≤ (yoshidaYInterval n).lower := by
  change 0 ≤ piFineInterval.lower * n / logTwoFineInterval.upper
  unfold piFineInterval logTwoFineInterval
  positivity

theorem scaledSineCauchyTermInterval_contains (n k : ℕ) :
    (scaledSineCauchyTermInterval n k).Contains
      (scaledSineCauchyTerm n k) := by
  have hy := yoshidaYInterval_contains n
  have hsInv := contains_inv_of_pos (I := sqrtTwoInterval)
    (x := Real.sqrt 2) (by norm_num [sqrtTwoInterval]) sqrtTwoInterval_contains
  have hfour : (pure ((4 : ℚ) ^ k)).Contains ((4 : ℝ) ^ k) := by
    simpa using contains_pure ((4 : ℚ) ^ k)
  have hfactor :
      (pure 1 - sqrtTwoInterval⁻¹ / pure ((4 : ℚ) ^ k)).Contains
        (1 - (Real.sqrt 2)⁻¹ / (4 : ℝ) ^ k) := by
    have hone : (RatInterval.pure (1 : ℚ)).Contains (1 : ℝ) :=
      by norm_num [Contains, RatInterval.pure]
    apply contains_sub hone
    exact contains_div_of_pos (by
      change 0 < (4 : ℚ) ^ k
      positivity) hsInv hfour
  have hx : (RatInterval.pure (quarterShiftQ k ^ 2)).Contains
      (((k : ℝ) + 1 / 4) ^ 2) := by
    norm_num [Contains, RatInterval.pure, quarterShiftQ]
  have hden : (cauchyDenomInterval n k).Contains
      (((k : ℝ) + 1 / 4) ^ 2 + yoshidaY n ^ 2) := by
    exact contains_add hx
      (contains_nonnegSquare (yoshidaYInterval_lower_nonneg n) hy)
  exact contains_div_of_pos (cauchyDenomInterval_lower_pos n k)
    (contains_mul hy hfactor) hden

def scaledCauchyHeadInterval (n : ℕ) : ℕ → RatInterval
  | 0 => pure 0
  | K + 1 => scaledCauchyHeadInterval n K + scaledSineCauchyTermInterval n K

theorem scaledCauchyHeadInterval_contains (n K : ℕ) :
    (scaledCauchyHeadInterval n K).Contains
      (∑ k ∈ Finset.range K, scaledSineCauchyTerm n k) := by
  induction K with
  | zero => norm_num [scaledCauchyHeadInterval, Contains, RatInterval.pure]
  | succ K ih =>
      rw [Finset.sum_range_succ]
      exact contains_add ih (scaledSineCauchyTermInterval_contains n K)

theorem scaledCauchyHeadInterval_contains_production
    {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (scaledCauchyHeadInterval n K).Contains
      (∑ k ∈ Finset.range K, sineCauchyTerm n k) := by
  convert scaledCauchyHeadInterval_contains n K using 1
  apply Finset.sum_congr rfl
  intro k _
  exact sineCauchyTerm_eq_scaled hn k

def scaledSinePolarValue (n : ℕ) : ℝ :=
  4 * yoshidaY n * (2 - Real.sqrt 2 - (Real.sqrt 2)⁻¹) /
    ((1 / 4 : ℝ) + 4 * yoshidaY n ^ 2)

theorem sinePolarValue_eq_scaled (n : ℕ) :
    sinePolarValue n = scaledSinePolarValue n := by
  rw [sinePolarValue, scaledSinePolarValue, yoshidaKappa_eq_two_mul_y]
  ring

def polarDenomInterval (n : ℕ) : RatInterval :=
  ⟨1 / 4 + 4 * (yoshidaYInterval n).lower ^ 2,
    1 / 4 + 4 * (yoshidaYInterval n).upper ^ 2⟩

theorem polarDenomInterval_lower_pos (n : ℕ) :
    0 < (polarDenomInterval n).lower := by
  change 0 < (1 / 4 : ℚ) + 4 * (yoshidaYInterval n).lower ^ 2
  positivity

def sinePolarInterval (n : ℕ) : RatInterval :=
  pure 4 * yoshidaYInterval n *
      (pure 2 - sqrtTwoInterval - sqrtTwoInterval⁻¹) /
    polarDenomInterval n

theorem sinePolarInterval_contains (n : ℕ) :
    (sinePolarInterval n).Contains (sinePolarValue n) := by
  rw [sinePolarValue_eq_scaled]
  have hy := yoshidaYInterval_contains n
  have hsInv := contains_inv_of_pos (I := sqrtTwoInterval)
    (x := Real.sqrt 2) (by norm_num [sqrtTwoInterval]) sqrtTwoInterval_contains
  have hcoeff :
      (pure 2 - sqrtTwoInterval - sqrtTwoInterval⁻¹).Contains
        (2 - Real.sqrt 2 - (Real.sqrt 2)⁻¹) := by
    exact contains_sub (contains_sub (by
      norm_num [Contains, RatInterval.pure]) sqrtTwoInterval_contains) hsInv
  have hden : (polarDenomInterval n).Contains
      ((1 / 4 : ℝ) + 4 * yoshidaY n ^ 2) := by
    have hsq := contains_nonnegSquare (yoshidaYInterval_lower_nonneg n) hy
    constructor
    · norm_num [polarDenomInterval, Contains, nonnegSquare] at hsq ⊢
      nlinarith [hsq.1]
    · norm_num [polarDenomInterval, Contains, nonnegSquare] at hsq ⊢
      nlinarith [hsq.2]
  exact contains_div_of_pos (polarDenomInterval_lower_pos n)
    (contains_mul (contains_mul (by norm_num [Contains, RatInterval.pure]) hy) hcoeff)
    hden

/-- The production scaled frequency is the `y = pi*n/log 2` used here. -/
theorem yoshidaScaledFrequency_eq_y (n : ℕ) :
    yoshidaScaledFrequency n = yoshidaY n := by
  rw [yoshidaScaledFrequency, yoshidaKappa_eq_two_mul_y]
  ring

def tailLowerFormulaInterval (n K : ℕ) : RatInterval :=
  let y := yoshidaYInterval n
  let x : ℚ := K + 1 / 4
  y / pure x - y * nonnegSquare y / pure (x ^ 3) -
    pure 2 * y / pure ((4 : ℚ) ^ K)

def tailUpperFormulaInterval (n K : ℕ) : RatInterval :=
  let y := yoshidaYInterval n
  let x : ℚ := K + 1 / 4
  y / pure x + y / pure (x ^ 2)

/-- Rational tail enclosure using the production `2*y/4^K` correction. -/
def cauchyTailInterval (n K : ℕ) : RatInterval :=
  ⟨(tailLowerFormulaInterval n K).lower,
    (tailUpperFormulaInterval n K).upper⟩

theorem tailLowerFormulaInterval_contains (n K : ℕ) :
    (tailLowerFormulaInterval n K).Contains
      (yoshidaY n / ((K : ℝ) + 1 / 4) -
        yoshidaY n ^ 3 / ((K : ℝ) + 1 / 4) ^ 3 -
        2 * yoshidaY n / (4 : ℝ) ^ K) := by
  have hy := yoshidaYInterval_contains n
  have hx : (pure (quarterShiftQ K)).Contains ((K : ℝ) + 1 / 4) := by
    norm_num [Contains, RatInterval.pure, quarterShiftQ]
  have hx3 : (pure (quarterShiftQ K ^ 3)).Contains
      (((K : ℝ) + 1 / 4) ^ 3) := by
    norm_num [Contains, RatInterval.pure, quarterShiftQ]
  have hy3 : (yoshidaYInterval n * nonnegSquare (yoshidaYInterval n)).Contains
      (yoshidaY n ^ 3) := by
    convert contains_mul hy
      (contains_nonnegSquare (yoshidaYInterval_lower_nonneg n) hy) using 1
    all_goals ring
  have hfour : (pure ((4 : ℚ) ^ K)).Contains ((4 : ℝ) ^ K) := by
    simpa using contains_pure ((4 : ℚ) ^ K)
  exact contains_sub
    (contains_sub
      (contains_div_of_pos (quarterShiftQ_pos K) hy hx)
      (contains_div_of_pos (pow_pos (quarterShiftQ_pos K) 3) hy3 hx3))
    (contains_div_of_pos (by
      change 0 < (4 : ℚ) ^ K
      positivity)
      (contains_mul (by norm_num [Contains, RatInterval.pure]) hy) hfour)

theorem tailUpperFormulaInterval_contains (n K : ℕ) :
    (tailUpperFormulaInterval n K).Contains
      (yoshidaY n / ((K : ℝ) + 1 / 4) +
        yoshidaY n / ((K : ℝ) + 1 / 4) ^ 2) := by
  have hy := yoshidaYInterval_contains n
  have hx : (pure (quarterShiftQ K)).Contains ((K : ℝ) + 1 / 4) := by
    norm_num [Contains, RatInterval.pure, quarterShiftQ]
  have hx2 : (pure (quarterShiftQ K ^ 2)).Contains
      (((K : ℝ) + 1 / 4) ^ 2) := by
    norm_num [Contains, RatInterval.pure, quarterShiftQ]
  exact contains_add
    (contains_div_of_pos (quarterShiftQ_pos K) hy hx)
    (contains_div_of_pos (pow_pos (quarterShiftQ_pos K) 2) hy hx2)

theorem cauchyTailInterval_contains
    {n K : ℕ} (hn : n ≠ 0) (hK : 0 < K) :
    (cauchyTailInterval n K).Contains
      (∑' j : ℕ, sineCauchyTerm n (K + j)) := by
  have ht := sineCauchyTerm_tail_bounds hn hK
  rw [yoshidaScaledFrequency_eq_y] at ht
  have hlo := tailLowerFormulaInterval_contains n K
  have hup := tailUpperFormulaInterval_contains n K
  exact ⟨hlo.1.trans ht.1, ht.2.trans hup.2⟩

def sineSeriesInterval (n K : ℕ) : RatInterval :=
  sinePolarInterval n -
    (scaledCauchyHeadInterval n K + cauchyTailInterval n K)

theorem sineSeriesInterval_contains
    {n K : ℕ} (hn : n ≠ 0) (hK : 0 < K) :
    (sineSeriesInterval n K).Contains (yoshidaSineMoment n) := by
  rw [yoshidaSineMoment_eq_finiteHead_sub_tail hn K]
  exact contains_sub (sinePolarInterval_contains n)
    (contains_add (scaledCauchyHeadInterval_contains_production hn K)
      (cauchyTailInterval_contains hn hK))

def IsSubinterval (I J : RatInterval) : Prop :=
  J.lower ≤ I.lower ∧ I.upper ≤ J.upper

instance (I J : RatInterval) : Decidable (IsSubinterval I J) :=
  inferInstanceAs (Decidable (J.lower ≤ I.lower ∧ I.upper ≤ J.upper))

theorem contains_of_subinterval
    {I J : RatInterval} {x : ℝ}
    (hIJ : IsSubinterval I J) (hx : I.Contains x) :
    J.Contains x := by
  have hl : (J.lower : ℝ) ≤ (I.lower : ℝ) := by
    exact_mod_cast hIJ.1
  have hu : (I.upper : ℝ) ≤ (J.upper : ℝ) := by
    exact_mod_cast hIJ.2
  exact ⟨hl.trans hx.1, hx.2.trans hu⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem sineSeriesInterval_192_sub_target
    {n : ℕ} (hn : 1 ≤ n) (hn10 : n ≤ 10) :
    IsSubinterval (sineSeriesInterval n 192) (yoshidaOddSineIntervals n) := by
  interval_cases n <;> decide +kernel

theorem sineTargetEnclosures_from_series192 :
    YoshidaOddSineTargetEnclosures := by
  intro n hn hn10
  exact contains_of_subinterval (sineSeriesInterval_192_sub_target hn hn10)
    (sineSeriesInterval_contains (by omega) (by norm_num))

end


end ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures
