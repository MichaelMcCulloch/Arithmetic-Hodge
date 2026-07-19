import ArithmeticHodge.Analysis.MultiplicativeWeilFourCellParityStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilMinimalFourCellBlockStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityStructural
import ArithmeticHodge.Analysis.YoshidaFourCellOddStripCapacityAssemblyStructural

set_option autoImplicit false

open Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFourCellCapacityAssemblyStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilFourCellParityStructural
open MultiplicativeWeilFourCellRealDiagonalStructural
open MultiplicativeWeilFourCellRealRescaleStructural
open MultiplicativeWeilFourCellSingleProfileStructural
open MultiplicativeWeilMinimalFourCellBlockStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotoneFourCellPrimeGeometryStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellEvenCapacityStructural
open YoshidaFourCellOddStripCapacityAssemblyStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural

/-!
# Production assembly from four-cell parity capacity

The analytic even and odd capacity inequalities act on the normalized real
profile of a four-cell block.  This file records that their sum is exactly the
complete Bombieri value and transports the result back to an arbitrary offset
inside a monotone quarter-cell decomposition.
-/

/-- Profile-specific even and odd lower-operator bounds imply nonnegativity of
the exact production four-cell Bombieri value. -/
theorem bombieriFunctional_fourBlock_re_nonnegative_of_parityCapacity
    (parent : BombieriTest) (k : ℤ)
    (hparent : bombieriConjugateTest parent = parent)
    (heven : 0 ≤ fourCellEvenPostPrimeLowerOperator
      (fourCellNormalizedEvenProfile parent k))
    (hodd : 0 ≤ fourCellOddStripCapacityLowerOperator
      (fourCellNormalizedOddProfile parent k)) :
    0 ≤ (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterFourBlock parent k))).re := by
  let e := fourCellNormalizedEvenProfile parent k
  let o := fourCellNormalizedOddProfile parent k
  have he : 0 ≤
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth e -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing e :=
    fourCellBracket_nonnegative_of_evenPostPrimeLowerOperator e
      (fourCellNormalizedEvenProfile_contDiff parent k).continuous
      ((fourCellNormalizedEvenProfile_contDiff parent k).contDiffOn
        |>.locallyLipschitzOn (convex_Icc (-1) 1))
      (fourCellNormalizedEvenProfile_even parent k) heven
  have ho : 0 ≤
      centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth o -
        Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing o :=
    fourCellBracket_nonnegative_of_oddStripCapacity o
      (fourCellNormalizedOddProfile_contDiff parent k)
      (fourCellNormalizedOddProfile_odd parent k) hodd
  have hsplit :=
    fourCell_centeredPhysical_sub_pairing_eq_parity parent k hparent
  have hbracket : 0 ≤
      centeredClippedPhysicalQuadratic (fourCellWholeHalfWidth k)
          (fourCellNormalizedRealProfile parent k) -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing (fourCellNormalizedRealProfile parent k) := by
    rw [hsplit]
    rw [fourCellWholeHalfWidth_eq]
    change 0 ≤
      (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth e -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing e) +
        (centeredClippedPhysicalQuadratic fourCellOperatorHalfWidth o -
          Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing o)
    exact add_nonneg he ho
  rw [bombieriFunctional_fourBlock_re_eq_centeredPhysical_sub_pairing
    parent k hparent]
  exact mul_nonneg (fourCellWholeHalfWidth_pos k).le hbracket

/-- A length-four block at offset `start` is the canonical four-cell block at
the corresponding physical lattice index. -/
theorem monotoneQuarterFiniteBlock_four_eq_fourBlock
    (parent : BombieriTest) (lo : ℤ) (start : ℕ) :
    monotoneQuarterFiniteBlock parent lo start 4 =
      monotoneQuarterFourBlock parent (lo + (start : ℤ)) := by
  classical
  unfold monotoneQuarterFiniteBlock monotoneQuarterFourBlock
  apply Finset.sum_congr rfl
  intro i _hi
  apply congrArg (monotoneQuarterCell parent)
  push_cast
  ring

/-- Universal parity capacity excludes every real-valued contiguous block of
the first possible negative length. -/
theorem bombieriRealQuadraticValue_fourBlock_nonnegative_of_parityCapacity
    (hEven : ∀ w : ℝ → ℝ, ContDiff ℝ 1 w → Function.Even w →
      0 ≤ fourCellEvenPostPrimeLowerOperator w)
    (hOdd : ∀ w : ℝ → ℝ, ContDiff ℝ 1 w → Function.Odd w →
      0 ≤ fourCellOddStripCapacityLowerOperator w)
    (parent : BombieriTest)
    (hparent : bombieriConjugateTest parent = parent)
    (lo : ℤ) (start : ℕ) :
    0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFiniteBlock parent lo start 4) := by
  let k : ℤ := lo + (start : ℤ)
  have hprod := bombieriFunctional_fourBlock_re_nonnegative_of_parityCapacity
    parent k hparent
    (hEven (fourCellNormalizedEvenProfile parent k)
      (fourCellNormalizedEvenProfile_contDiff parent k)
      (fourCellNormalizedEvenProfile_even parent k))
    (hOdd (fourCellNormalizedOddProfile parent k)
      (fourCellNormalizedOddProfile_contDiff parent k)
      (fourCellNormalizedOddProfile_odd parent k))
  unfold bombieriRealQuadraticValue
  rw [monotoneQuarterFiniteBlock_four_eq_fourBlock parent lo start]
  exact hprod

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFourCellCapacityAssemblyStructural
