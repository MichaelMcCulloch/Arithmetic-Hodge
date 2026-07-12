import ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceCheckDefs

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks

noncomputable section

open YoshidaEvenSparseCongruenceData
open SparseEntriesCertificate

/-- The computable pair-list form of the robust off-diagonal radius. -/
def evenSparseEntryRadiusEntries (i j : YoshidaEvenIndex) : ℚ :=
  |evenSparseCenterCongruenceEntries i j| +
    evenSparseEpsilon * evenSparseRowL1 i * evenSparseRowL1 j

/-- The computable pair-list form of the robust transformed diagonal lower
bound. -/
def evenSparseDiagonalLowerEntries (i : YoshidaEvenIndex) : ℚ :=
  evenSparseCenterCongruenceEntries i i -
    evenSparseEpsilon * evenSparseRowL1 i ^ 2

/-- Exact weighted dominance stated only through the computable canonical
pair-list payload. -/
abbrev EvenSparseWeightedDominanceEntriesAt (i : YoshidaEvenIndex) : Prop :=
  (∑ j ∈ Finset.univ.erase i,
      evenSparseEntryRadiusEntries i j * evenSparseWeights j) <
    evenSparseDiagonalLowerEntries i * evenSparseWeights i

/-- The kernel-computable pair-list congruence is exactly the original
`Finsupp` congruence used by the public certificate predicate. -/
theorem evenSparseCenterCongruence_eq_entries
    (i j : YoshidaEvenIndex) :
    evenSparseCenterCongruence i j =
      evenSparseCenterCongruenceEntries i j := by
  simpa [evenSparseCenterCongruence, evenSparseCenterCongruenceEntries,
    evenSparseRows] using
    sparseCongruenceEntry_rowOfEntries evenSparseEntries
      evenTargetCenter i j

theorem evenSparseEntryRadius_eq_entries
    (i j : YoshidaEvenIndex) :
    evenSparseEntryRadius i j = evenSparseEntryRadiusEntries i j := by
  simp only [evenSparseEntryRadius, evenSparseEntryRadiusEntries,
    evenSparseCenterCongruence_eq_entries]

theorem evenSparseDiagonalLower_eq_entries
    (i : YoshidaEvenIndex) :
    evenSparseDiagonalLower i = evenSparseDiagonalLowerEntries i := by
  simp only [evenSparseDiagonalLower, evenSparseDiagonalLowerEntries,
    evenSparseCenterCongruence_eq_entries]

/-- The computable dominance certificate proves the original public
`Finsupp`-based dominance statement without changing its semantics. -/
theorem evenSparseWeightedDominanceAt_iff_entries
    (i : YoshidaEvenIndex) :
    EvenSparseWeightedDominanceAt i ↔
      EvenSparseWeightedDominanceEntriesAt i := by
  simp only [EvenSparseWeightedDominanceAt,
    EvenSparseWeightedDominanceEntriesAt,
    evenSparseEntryRadius_eq_entries,
    evenSparseDiagonalLower_eq_entries]

theorem evenSparseWeightedDominanceAt_of_entries
    {i : YoshidaEvenIndex}
    (h : EvenSparseWeightedDominanceEntriesAt i) :
    EvenSparseWeightedDominanceAt i :=
  (evenSparseWeightedDominanceAt_iff_entries i).2 h

end

end ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks
