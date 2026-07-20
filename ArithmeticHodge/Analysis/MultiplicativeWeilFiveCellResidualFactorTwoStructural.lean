import ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellResidualDeterminantClosureStructural

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellResidualFactorTwoStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilAllLengthEndpointReserveStructural
open MultiplicativeWeilBelowThreePrimeReductionStructural
open MultiplicativeWeilFiveCellResidualDeterminantClosureStructural
open MultiplicativeWeilMinimalNegativeBlockStructural
open MultiplicativeWeilMonotonePrimeAtomAggregateObstructionStructural
open MultiplicativeWeilMonotoneQuarterPartitionStructural
open MultiplicativeWeilQuarterLogLatticePartitionStructural
open MultiplicativeWeilRealMonotonePropagationCriterionStructural

/-!
# The five-cell residual pencil is exactly a factor-two problem

Five consecutive monotone quarter-cells occupy a multiplicative interval of
ratio `2 * sqrt 2 < 3`.  Consequently every such block, including every
middle-orthogonal residual pencil realized by a modified common parent, has
only the `p = 2` atom in its prime functional.  This file exposes that exact
non-circular analytic target.
-/

private theorem tsupport_finset_sum_subset_Icc_fiveCell
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → BombieriTest) (a b : ℝ)
    (hf : ∀ i ∈ s, tsupport (f i) ⊆ Icc a b) :
    tsupport (((∑ i ∈ s, f i) : BombieriTest) : ℝ → ℂ) ⊆ Icc a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (tsupport_add (f i : ℝ → ℂ)
          (∑ j ∈ s, f j : BombieriTest)).trans
        (union_subset (hf i (by simp))
          (ih (fun j hj ↦ hf j (by simp [hj]))))

/-- A five-cell block is supported between the first boundary and the sixth
later quarter-lattice point. -/
theorem monotoneQuarterFiveBlock_tsupport_subset
    (parent : BombieriTest) (k : ℤ) :
    tsupport (monotoneQuarterFiveBlock parent k) ⊆
      Icc (quarterLogLatticePoint k)
        (quarterLogLatticePoint (k + 6)) := by
  classical
  unfold monotoneQuarterFiveBlock monotoneQuarterFiniteBlock
  apply tsupport_finset_sum_subset_Icc_fiveCell
  intro i hi
  have hiFive : i < 5 := Finset.mem_range.mp hi
  have hcell := monotoneQuarterCell_tsupport_subset parent
    (k + ((i : ℕ) : ℤ))
  simpa only [Nat.zero_add] using hcell.trans (Icc_subset_Icc
    (quarterLogLatticePoint_mono (by omega))
    (quarterLogLatticePoint_mono (by omega)))

/-- The exact support ratio of a five-cell block is strictly below three. -/
theorem monotoneQuarterFiveBlock_endpoint_ratio_lt_three (k : ℤ) :
    quarterLogLatticePoint (k + 6) /
        quarterLogLatticePoint k < 3 := by
  have hkpos := quarterLogLatticePoint_pos k
  have hsq : quarterLogLatticePoint 2 ^ 2 = 2 := by
    calc
      quarterLogLatticePoint 2 ^ 2 =
          quarterLogLatticePoint 2 * quarterLogLatticePoint 2 := by ring
      _ = quarterLogLatticePoint (2 + 2) :=
        (quarterLogLatticePoint_add 2 2).symm
      _ = 2 := by norm_num [quarterLogLatticePoint_four]
  have hsqrtBound : quarterLogLatticePoint 2 < (3 / 2 : ℝ) := by
    nlinarith [quarterLogLatticePoint_pos 2]
  calc
    quarterLogLatticePoint (k + 6) /
          quarterLogLatticePoint k = quarterLogLatticePoint 6 := by
      rw [quarterLogLatticePoint_add]
      field_simp [hkpos.ne']
    _ = 2 * quarterLogLatticePoint 2 := by
      rw [show (6 : ℤ) = 2 + 4 by norm_num,
        quarterLogLatticePoint_add, quarterLogLatticePoint_four]
    _ < 3 := by nlinarith

/-- Exact below-three formula for every five-cell production block: no prime
other than the factor-two dilation remains. -/
theorem bombieriFunctional_fiveBlock_re_eq_localCritical_sub_factorTwo
    (parent : BombieriTest) (k : ℤ) :
    (bombieriFunctional
      (bombieriQuadraticTest (monotoneQuarterFiveBlock parent k))).re =
      (bombieriLocalCriticalForm
        (monotoneQuarterFiveBlock parent k)
        (monotoneQuarterFiveBlock parent k)).re -
      Real.sqrt 2 * Real.log 2 *
        (criticalDilationCorrelation
          (monotoneQuarterFiveBlock parent k) 2).re := by
  exact
    bombieriFunctional_quadratic_re_eq_localCritical_sub_dilationCorrelation
      (monotoneQuarterFiveBlock parent k)
      (a := quarterLogLatticePoint k)
      (b := quarterLogLatticePoint (k + 6))
      (quarterLogLatticePoint_pos k)
      (quarterLogLatticePoint_mono (by omega))
      (monotoneQuarterFiveBlock_tsupport_subset parent k)
      (monotoneQuarterFiveBlock_endpoint_ratio_lt_three k)

/-- Five-cell production positivity is exactly local critical domination of
the single factor-two atom. -/
theorem bombieriRealQuadraticValue_fiveBlock_nonnegative_iff_factorTwoDomination
    (parent : BombieriTest) (k : ℤ) :
    0 ≤ bombieriRealQuadraticValue (monotoneQuarterFiveBlock parent k) ↔
      Real.sqrt 2 * Real.log 2 *
          (criticalDilationCorrelation
            (monotoneQuarterFiveBlock parent k) 2).re ≤
        (bombieriLocalCriticalForm
          (monotoneQuarterFiveBlock parent k)
          (monotoneQuarterFiveBlock parent k)).re := by
  unfold bombieriRealQuadraticValue
  rw [bombieriFunctional_fiveBlock_re_eq_localCritical_sub_factorTwo]
  constructor <;> intro h <;> linarith

/-! ## Lossless routing of the five-cell determinant -/

/-- The first all-length analytic target with the global Bombieri functional
eliminated: on every real five-cell common parent, the local critical form
must dominate the unique factor-two atom. -/
def RealFiveCellFactorTwoDomination : Prop :=
  ∀ parent : BombieriTest,
    bombieriConjugateTest parent = parent →
      ∀ k : ℤ,
        Real.sqrt 2 * Real.log 2 *
            (criticalDilationCorrelation
              (monotoneQuarterFiveBlock parent k) 2).re ≤
          (bombieriLocalCriticalForm
            (monotoneQuarterFiveBlock parent k)
            (monotoneQuarterFiveBlock parent k)).re

/-- Universal five-cell factor-two domination is exactly universal five-cell
production positivity.  The forward direction is non-circular because the
domination statement mentions only the local critical form and one explicit
dilation correlation. -/
theorem realFiveCellFactorTwoDomination_iff_productionNonnegative :
    RealFiveCellFactorTwoDomination ↔
      RealFiniteBlockProductionNonnegativeAtLength 5 := by
  constructor
  · intro hdom parent hparent k
    change 0 ≤ bombieriRealQuadraticValue
      (monotoneQuarterFiveBlock parent k)
    exact
      (bombieriRealQuadraticValue_fiveBlock_nonnegative_iff_factorTwoDomination
        parent k).2 (hdom parent hparent k)
  · intro hproduction parent hparent k
    apply
      (bombieriRealQuadraticValue_fiveBlock_nonnegative_iff_factorTwoDomination
        parent k).1
    exact hproduction parent hparent k

/-- Once production through length four is available, the first genuine
common-parent residual determinant is losslessly the explicit factor-two
domination problem above. -/
theorem realFiveCellFactorTwoDomination_iff_commonParentContraction
    (hprev : RealFiniteBlockProductionNonnegativeUpTo 4) :
    RealFiveCellFactorTwoDomination ↔
      RealFiveCellCommonParentMiddlePivotResidualContraction := by
  exact realFiveCellFactorTwoDomination_iff_productionNonnegative.trans
    (fiveCell_productionNonnegative_iff_commonParentContraction hprev)

end

end ArithmeticHodge.Analysis.MultiplicativeWeilFiveCellResidualFactorTwoStructural
