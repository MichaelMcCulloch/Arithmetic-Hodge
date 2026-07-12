import ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceDominanceDefs
import ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceStructure

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks

open SparseEntriesCertificate
open YoshidaEvenSparseCongruenceData

/-- Use one residue block per stored coefficient in the row.  This keeps every
kernel check near a constant sparse-product budget. -/
def evenSparseDominanceBlockCount (i : YoshidaEvenIndex) : ℕ :=
  (evenSparseEntries i).length

def evenSparseDominanceBlock (i : YoshidaEvenIndex) (b : ℕ) :
    Finset YoshidaEvenIndex :=
  (Finset.univ.erase i).filter fun j ↦
    j.1 % evenSparseDominanceBlockCount i = b

def evenSparseDominanceBlockContribution
    (i : YoshidaEvenIndex) (b : ℕ) : ℚ :=
  ∑ j ∈ evenSparseDominanceBlock i b,
    evenSparseEntryRadiusEntries i j * evenSparseWeights j

theorem evenSparseDominanceBlockCount_pos (i : YoshidaEvenIndex) :
    0 < evenSparseDominanceBlockCount i := by
  have hdiag := (evenSparseRowStructureAt i).2.2
  unfold EvenSparseDiagonalPositiveAt at hdiag
  change 0 < rowOfEntries (evenSparseEntries i) i at hdiag
  have hmem : i ∈ (evenSparseEntries i).map Prod.fst :=
    mem_map_fst_of_rowOfEntries_apply_ne_zero hdiag.ne'
  unfold evenSparseDominanceBlockCount
  exact List.length_pos_iff_ne_nil.mpr fun hnil ↦ by
    rw [hnil] at hmem
    simp at hmem

/-- The residue blocks partition the complete off-diagonal row exactly. -/
theorem sum_evenSparseDominanceBlockContribution (i : YoshidaEvenIndex) :
    (∑ b ∈ Finset.range (evenSparseDominanceBlockCount i),
        evenSparseDominanceBlockContribution i b) =
      ∑ j ∈ Finset.univ.erase i,
        evenSparseEntryRadiusEntries i j * evenSparseWeights j := by
  let s : Finset YoshidaEvenIndex := Finset.univ.erase i
  let c : ℕ := evenSparseDominanceBlockCount i
  have hc : 0 < c := by
    simpa only [c] using evenSparseDominanceBlockCount_pos i
  have hmap : ∀ j ∈ s, j.1 % c ∈ Finset.range c := by
    intro j _hj
    exact Finset.mem_range.mpr (Nat.mod_lt _ hc)
  have h := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := Finset.range c) (g := fun j : YoshidaEvenIndex ↦ j.1 % c)
    hmap (fun j ↦ evenSparseEntryRadiusEntries i j * evenSparseWeights j)
  simpa [evenSparseDominanceBlockContribution, evenSparseDominanceBlock,
    s, c] using h

theorem evenSparseWeightedDominanceEntriesAt_iff_blocks
    (i : YoshidaEvenIndex) :
    EvenSparseWeightedDominanceEntriesAt i ↔
      (∑ b ∈ Finset.range (evenSparseDominanceBlockCount i),
          evenSparseDominanceBlockContribution i b) <
        evenSparseDiagonalLowerEntries i * evenSparseWeights i := by
  unfold EvenSparseWeightedDominanceEntriesAt
  rw [sum_evenSparseDominanceBlockContribution]

end ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks
