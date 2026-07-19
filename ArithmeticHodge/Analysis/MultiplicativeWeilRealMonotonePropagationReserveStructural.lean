import ArithmeticHodge.Analysis.MultiplicativeWeilMonotoneRealCutContractionAttemptStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationCriterionStructural

set_option autoImplicit false

open Complex Real

namespace ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationReserveStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilMonotoneCutPrimePhaseStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilMonotoneRealCutContractionAttemptStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# The arithmetic-mean reserve at one real monotone cut

For the selected cutoff, write the outer test as its ratio-two head cell plus
the whole inner suffix.  Its quadratic value is

`H + T + 2 X`,

where `H` is the unconditionally nonnegative head value, `T` is the suffix
value assumed nonnegative by backward propagation, and `X` is the real global
cross.  Therefore the exact one-step target is only `-2 X <= H + T`.

This is weaker than the phase-uniform determinant estimate `X^2 <= H*T`.
Conversely, an actual failure of propagation forces `X < 0` and the strict
determinant reversal `H*T < X^2`.  Thus the imbalance between the head and
suffix diagonals is a genuine reserve which the determinant route discards.
-/

/-- Quadratic value of the ratio-two head at one monotone cut. -/
def monotoneQuarterHeadQuadraticValue
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  bombieriRealQuadraticValue (monotoneQuarterCell parent k)

/-- Quadratic value of the whole inner suffix. -/
def monotoneQuarterSuffixQuadraticValue
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  bombieriRealQuadraticValue (monotoneQuarterCutoff parent (k + 1))

/-- Real global cross between the ratio-two head and the whole inner suffix. -/
def monotoneQuarterHeadSuffixCrossValue
    (parent : BombieriTest) (k : ℤ) : ℝ :=
  (bombieriTwoBlockGlobalCrossSymbol
    (monotoneQuarterCell parent k)
    (monotoneQuarterCutoff parent (k + 1))).re

/-- Exact head--suffix expansion of the selected outer cutoff. -/
theorem bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_head_suffix_cross
    (parent : BombieriTest) (k : ℤ) :
    bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) =
      monotoneQuarterHeadQuadraticValue parent k +
        monotoneQuarterSuffixQuadraticValue parent k +
          2 * monotoneQuarterHeadSuffixCrossValue parent k := by
  have h :=
    bombieriFunctional_monotoneCutPencil_ofReal_re_eq_head_cross_suffix
      parent k 0
  simpa only [monotoneCutPencil, Complex.ofReal_zero, zero_smul, add_zero,
    zero_add, one_pow, one_mul, bombieriRealQuadraticValue,
    mul_one,
    monotoneQuarterHeadQuadraticValue,
    monotoneQuarterSuffixQuadraticValue,
    monotoneQuarterHeadSuffixCrossValue] using h

/-- The head diagonal is nonnegative without a hypothesis on the parent. -/
theorem monotoneQuarterHeadQuadraticValue_nonnegative
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ monotoneQuarterHeadQuadraticValue parent k := by
  exact bombieriFunctional_monotoneQuarterCell_re_nonnegative parent k

private theorem determinant_reversal_of_sum_cross_negative
    {H T X : ℝ} (hH : 0 ≤ H) (hT : 0 ≤ T)
    (hneg : H + T + 2 * X < 0) :
    H * T < X ^ 2 := by
  have hX : X < 0 := by linarith
  nlinarith [sq_nonneg (H - T), sq_nonneg (H + T + 2 * X)]

private theorem arithmetic_reserve_identity
    {H T X : ℝ} (hden : H + T - 2 * X ≠ 0) :
    H + T + 2 * X =
      ((H - T) ^ 2 + 4 * (H * T - X ^ 2)) /
        (H + T - 2 * X) := by
  field_simp [hden]
  ring

/-- The arithmetic-mean cross bound is exactly sufficient for the selected
one-step propagation. -/
theorem bombieriRealQuadraticValue_monotoneQuarterCutoff_nonnegative_of_cross
    (parent : BombieriTest) (k : ℤ)
    (hcross :
      -2 * monotoneQuarterHeadSuffixCrossValue parent k ≤
        monotoneQuarterHeadQuadraticValue parent k +
          monotoneQuarterSuffixQuadraticValue parent k) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) := by
  rw [bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_head_suffix_cross]
  linarith

/-- A negative outer cutoff necessarily has a strictly negative global
head--suffix cross. -/
theorem monotoneQuarterHeadSuffixCrossValue_negative_of_outer_negative
    (parent : BombieriTest) (k : ℤ)
    (hsuffix : 0 ≤ monotoneQuarterSuffixQuadraticValue parent k)
    (houter : bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent k) < 0) :
    monotoneQuarterHeadSuffixCrossValue parent k < 0 := by
  have hhead := monotoneQuarterHeadQuadraticValue_nonnegative parent k
  rw [bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_head_suffix_cross]
    at houter
  linarith

/-- On the only adverse branch `X < 0`, propagation is exactly the sign of a
sum of two reserves: the squared diagonal imbalance and four times the
determinant margin.  A negative determinant margin is therefore harmless
until it exceeds the imbalance reserve. -/
theorem bombieriRealQuadraticValue_monotoneQuarterCutoff_nonnegative_iff_reserve
    (parent : BombieriTest) (k : ℤ)
    (hsuffix : 0 ≤ monotoneQuarterSuffixQuadraticValue parent k)
    (hcross : monotoneQuarterHeadSuffixCrossValue parent k < 0) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) ↔
      0 ≤
        (monotoneQuarterHeadQuadraticValue parent k -
            monotoneQuarterSuffixQuadraticValue parent k) ^ 2 +
          4 *
            (monotoneQuarterHeadQuadraticValue parent k *
                monotoneQuarterSuffixQuadraticValue parent k -
              (monotoneQuarterHeadSuffixCrossValue parent k) ^ 2) := by
  let H := monotoneQuarterHeadQuadraticValue parent k
  let T := monotoneQuarterSuffixQuadraticValue parent k
  let X := monotoneQuarterHeadSuffixCrossValue parent k
  have hH : 0 ≤ H := monotoneQuarterHeadQuadraticValue_nonnegative parent k
  have hT : 0 ≤ T := hsuffix
  have hX : X < 0 := hcross
  have hden : 0 < H + T - 2 * X := by linarith
  rw [bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_head_suffix_cross]
  change 0 ≤ H + T + 2 * X ↔
    0 ≤ (H - T) ^ 2 + 4 * (H * T - X ^ 2)
  rw [arithmetic_reserve_identity hden.ne']
  constructor
  · intro hquot
    rcases (div_nonneg_iff.mp hquot) with hpos | hneg
    · exact hpos.1
    · exact (not_le_of_gt hden hneg.2).elim
  · intro hnum
    exact div_nonneg hnum hden.le

/-- More sharply, any failure of one-step propagation forces strict reversal
of the stronger phase-uniform determinant inequality. -/
theorem monotoneQuarter_head_suffix_determinant_reversal_of_outer_negative
    (parent : BombieriTest) (k : ℤ)
    (hsuffix : 0 ≤ monotoneQuarterSuffixQuadraticValue parent k)
    (houter : bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent k) < 0) :
    monotoneQuarterHeadQuadraticValue parent k *
        monotoneQuarterSuffixQuadraticValue parent k <
      (monotoneQuarterHeadSuffixCrossValue parent k) ^ 2 := by
  apply determinant_reversal_of_sum_cross_negative
    (monotoneQuarterHeadQuadraticValue_nonnegative parent k) hsuffix
  rw [← bombieriRealQuadraticValue_monotoneQuarterCutoff_eq_head_suffix_cross]
  exact houter

/-- The stronger determinant bound closes propagation, but the preceding
arithmetic-mean theorem records precisely how much stronger it is. -/
theorem bombieriRealQuadraticValue_monotoneQuarterCutoff_nonnegative_of_det
    (parent : BombieriTest) (k : ℤ)
    (hsuffix : 0 ≤ monotoneQuarterSuffixQuadraticValue parent k)
    (hdet :
      (monotoneQuarterHeadSuffixCrossValue parent k) ^ 2 ≤
        monotoneQuarterHeadQuadraticValue parent k *
          monotoneQuarterSuffixQuadraticValue parent k) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterCutoff parent k) := by
  by_contra hnot
  have houter : bombieriRealQuadraticValue
      (monotoneQuarterCutoff parent k) < 0 := lt_of_not_ge hnot
  have hrev :=
    monotoneQuarter_head_suffix_determinant_reversal_of_outer_negative
      parent k hsuffix houter
  exact (not_lt_of_ge hdet) hrev

end

end ArithmeticHodge.Analysis.MultiplicativeWeilRealMonotonePropagationReserveStructural
