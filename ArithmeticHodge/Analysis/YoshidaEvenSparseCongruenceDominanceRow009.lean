import ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceDominanceBlocksRow009

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks

open YoshidaEvenSparseCongruenceData

private theorem evenSparseDominanceBudgetMargin_row009 :
    (∑ b ∈ Finset.range
        (evenSparseDominanceBlockCount (9 : YoshidaEvenIndex)),
      evenSparseDominanceBlockBudget (9 : YoshidaEvenIndex) b) <
        evenSparseDiagonalLowerEntries (9 : YoshidaEvenIndex) *
          evenSparseWeights (9 : YoshidaEvenIndex) := by
  decide +kernel

theorem evenSparseWeightedDominanceEntries_row009 :
    EvenSparseWeightedDominanceEntriesAt (9 : YoshidaEvenIndex) := by
  apply (evenSparseWeightedDominanceEntriesAt_iff_blocks _).2
  calc
    (∑ b ∈ Finset.range
        (evenSparseDominanceBlockCount (9 : YoshidaEvenIndex)),
      evenSparseDominanceBlockContribution (9 : YoshidaEvenIndex) b) ≤
        ∑ b ∈ Finset.range
          (evenSparseDominanceBlockCount (9 : YoshidaEvenIndex)),
          evenSparseDominanceBlockBudget (9 : YoshidaEvenIndex) b := by
      apply Finset.sum_le_sum
      intro b hb
      have hcount :
          evenSparseDominanceBlockCount (9 : YoshidaEvenIndex) = 10 := by
        decide +kernel
      have hb10 : b < 10 := by
        rw [hcount] at hb
        exact Finset.mem_range.mp hb
      interval_cases b
      all_goals first
        | exact evenSparseDominanceBlock_row009_000_le
        | exact evenSparseDominanceBlock_row009_001_le
        | exact evenSparseDominanceBlock_row009_002_le
        | exact evenSparseDominanceBlock_row009_003_le
        | exact evenSparseDominanceBlock_row009_004_le
        | exact evenSparseDominanceBlock_row009_005_le
        | exact evenSparseDominanceBlock_row009_006_le
        | exact evenSparseDominanceBlock_row009_007_le
        | exact evenSparseDominanceBlock_row009_008_le
        | exact evenSparseDominanceBlock_row009_009_le
    _ < evenSparseDiagonalLowerEntries (9 : YoshidaEvenIndex) *
          evenSparseWeights (9 : YoshidaEvenIndex) :=
      evenSparseDominanceBudgetMargin_row009

theorem evenSparseWeightedDominance_row009 :
    EvenSparseWeightedDominanceAt (9 : YoshidaEvenIndex) :=
  evenSparseWeightedDominanceAt_of_entries
    evenSparseWeightedDominanceEntries_row009

end ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks
