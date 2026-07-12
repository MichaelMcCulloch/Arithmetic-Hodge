import ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceData

set_option autoImplicit false

open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks

noncomputable section

open SparseCongruenceCertificate
open YoshidaEvenSparseCongruenceData

def evenTargetHalfWidth (i j : YoshidaEvenIndex) : ℚ :=
  ((evenTargetInterval i j).upper - (evenTargetInterval i j).lower) / 2

def EvenTargetRadiusBoundAt (i j : YoshidaEvenIndex) : Prop :=
  evenTargetHalfWidth i j ≤ evenSparseEpsilon

def EvenTargetCenterSymmetricAt (i j : YoshidaEvenIndex) : Prop :=
  evenTargetCenter i j = evenTargetCenter j i

def EvenSparseWeightPositiveAt (i : YoshidaEvenIndex) : Prop :=
  0 < evenSparseWeights i

def EvenSparseLowerTriangularAt
    (i j : YoshidaEvenIndex) : Prop :=
  evenSparseRows i j ≠ 0 → j ≤ i

def EvenSparseDiagonalPositiveAt (i : YoshidaEvenIndex) : Prop :=
  0 < evenSparseRows i i

def evenSparseEntryRadius (i j : YoshidaEvenIndex) : ℚ :=
  |sparseCongruenceEntry evenSparseRows evenTargetCenter i j| +
    evenSparseEpsilon * evenSparseRowL1 i * evenSparseRowL1 j

def evenSparseDiagonalLower (i : YoshidaEvenIndex) : ℚ :=
  sparseCongruenceEntry evenSparseRows evenTargetCenter i i -
    evenSparseEpsilon * evenSparseRowL1 i ^ 2

def EvenSparseWeightedDominanceAt (i : YoshidaEvenIndex) : Prop :=
  (∑ j ∈ Finset.univ.erase i,
      evenSparseEntryRadius i j * evenSparseWeights j) <
    evenSparseDiagonalLower i * evenSparseWeights i

def EvenTargetRadiusBoundRow (i : YoshidaEvenIndex) : Prop :=
  ∀ j, EvenTargetRadiusBoundAt i j

def EvenTargetCenterSymmetricRow (i : YoshidaEvenIndex) : Prop :=
  ∀ j, EvenTargetCenterSymmetricAt i j

def EvenSparseRowStructureAt (i : YoshidaEvenIndex) : Prop :=
  EvenSparseWeightPositiveAt i ∧
    (∀ j, EvenSparseLowerTriangularAt i j) ∧
    EvenSparseDiagonalPositiveAt i

end

end ArithmeticHodge.Analysis.YoshidaEvenSparseCongruenceChecks
