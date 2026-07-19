import ArithmeticHodge.Analysis.MultiplicativeWeilCellChainCriterionClosure
import Mathlib.Data.List.Sort

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# A partition-selected cell-chain criterion

The universal cell-chain condition asks for every ratio-two cell list to
contract.  Assembly needs much less: for each test it is enough that one
ratio-two decomposition, in one chosen order, satisfies the recursive
head--whole-tail inequalities.  This file records that exact existential
criterion and shows that the order may additionally be chosen monotonically
by a concrete support key.

This does not prove the missing contraction.  It identifies the weakest
partition-level target exposed by the current finite assembly theorem, while
leaving both the partition and its order available for a structural argument.
-/

/-- The deterministic key used to order cells: the infimum of the topological
support.  It is defined for the zero test as well (with Lean's usual `sInf`
convention), which keeps the sorting operation total. -/
def bombieriCellLeftSupportKey (g : BombieriTest) : ℝ :=
  sInf (tsupport g)

/-- A ratio-two decomposition of one test for which one chosen list order
satisfies the recursive head--whole-tail contraction. -/
def BombieriAdmitsContractingRatioTwoDecomposition (g : BombieriTest) : Prop :=
  ∃ cells : List BombieriTest,
    cells.sum = g ∧
      (∀ f ∈ cells, BombieriRatioTwoCell f) ∧
        BombieriCellChainContraction cells

/-- The weakest direct partition-level hypothesis consumed by the existing
finite-cell assembly theorem: every test gets one successful decomposition. -/
def BombieriEveryTestAdmitsContractingRatioTwoDecomposition : Prop :=
  ∀ g : BombieriTest, BombieriAdmitsContractingRatioTwoDecomposition g

/-- A more concrete selected decomposition: its cells are ordered from left to
right by the infimum of their topological supports. -/
def BombieriAdmitsLeftOrderedContractingRatioTwoDecomposition
    (g : BombieriTest) : Prop :=
  ∃ cells : List BombieriTest,
    cells.sum = g ∧
      (∀ f ∈ cells, BombieriRatioTwoCell f) ∧
        cells.Pairwise
          (fun f h ↦ bombieriCellLeftSupportKey f ≤
            bombieriCellLeftSupportKey h) ∧
          BombieriCellChainContraction cells

/-- Every test admits a contracting ratio-two decomposition in concrete
left-support order. -/
def BombieriEveryTestAdmitsLeftOrderedContractingRatioTwoDecomposition : Prop :=
  ∀ g : BombieriTest,
    BombieriAdmitsLeftOrderedContractingRatioTwoDecomposition g

/-- The same recursive cut condition written in the form most directly
available for a partition-of-unity argument: at every ordered cut, the whole
complex pencil formed by the head and the suffix sum is nonnegative. -/
def BombieriCellChainPencilNonnegative : List BombieriTest → Prop
  | [] => True
  | [_] => True
  | f :: g :: rest =>
      BombieriCellChainPencilNonnegative (g :: rest) ∧
        ∀ c : ℂ,
          0 ≤ (bombieriFunctional
            (bombieriQuadraticTest (f + c • (g :: rest).sum))).re

/-- On ratio-two cells, recursive determinant contractions are exactly the
recursive cut-pencil inequalities.  For cells cut from one test by a smooth
partition of unity, the latter keeps visible that both blocks are correlated
pieces of the same seed. -/
theorem bombieriCellChainContraction_iff_cutPencilNonnegative
    (cells : List BombieriTest)
    (hcells : ∀ g ∈ cells, BombieriRatioTwoCell g) :
    BombieriCellChainContraction cells ↔
      BombieriCellChainPencilNonnegative cells := by
  induction cells with
  | nil => simp [BombieriCellChainContraction,
      BombieriCellChainPencilNonnegative]
  | cons f tail ih =>
      cases tail with
      | nil => simp [BombieriCellChainContraction,
          BombieriCellChainPencilNonnegative]
      | cons g rest =>
          have hf :
              0 ≤ (bombieriFunctional (bombieriQuadraticTest f)).re :=
            bombieriFunctional_quadratic_re_nonneg_of_ratioTwoCell f
              (hcells f (by simp))
          have htailCells :
              ∀ h ∈ g :: rest, BombieriRatioTwoCell h := by
            intro h hh
            exact hcells h (List.mem_cons_of_mem f hh)
          have hiffTail :
              BombieriCellChainContraction (g :: rest) ↔
                BombieriCellChainPencilNonnegative (g :: rest) :=
            ih htailCells
          constructor
          · intro hchain
            change
              BombieriCellChainContraction (g :: rest) ∧
                Complex.normSq
                    (bombieriTwoBlockGlobalCrossSymbol f (g :: rest).sum) ≤
                  (bombieriFunctional (bombieriQuadraticTest f)).re *
                    (bombieriFunctional
                      (bombieriQuadraticTest (g :: rest).sum)).re at hchain
            have htail :
                0 ≤ (bombieriFunctional
                  (bombieriQuadraticTest (g :: rest).sum)).re :=
              bombieriFunctional_quadratic_re_nonneg_of_cellChain
                (g :: rest) htailCells hchain.1
            change
              BombieriCellChainPencilNonnegative (g :: rest) ∧
                ∀ c : ℂ,
                  0 ≤ (bombieriFunctional
                    (bombieriQuadraticTest
                      (f + c • (g :: rest).sum))).re
            exact ⟨hiffTail.1 hchain.1,
              (bombieriFunctional_twoBlock_nonneg_iff
                f (g :: rest).sum hf htail).2 hchain.2⟩
          · intro hpencil
            change
              BombieriCellChainPencilNonnegative (g :: rest) ∧
                ∀ c : ℂ,
                  0 ≤ (bombieriFunctional
                    (bombieriQuadraticTest
                      (f + c • (g :: rest).sum))).re at hpencil
            have htailChain := hiffTail.2 hpencil.1
            have htail :
                0 ≤ (bombieriFunctional
                  (bombieriQuadraticTest (g :: rest).sum)).re :=
              bombieriFunctional_quadratic_re_nonneg_of_cellChain
                (g :: rest) htailCells htailChain
            change
              BombieriCellChainContraction (g :: rest) ∧
                Complex.normSq
                    (bombieriTwoBlockGlobalCrossSymbol f (g :: rest).sum) ≤
                  (bombieriFunctional (bombieriQuadraticTest f)).re *
                    (bombieriFunctional
                      (bombieriQuadraticTest (g :: rest).sum)).re
            exact ⟨htailChain,
              (bombieriFunctional_twoBlock_nonneg_iff
                f (g :: rest).sum hf htail).1 hpencil.2⟩

/-- Partition-selected criterion in cut-pencil coordinates.  This is the
form suited to a retained partition of unity: each required test is a head
cell plus a scalar multiple of the sum of all cells to its right. -/
def BombieriEveryTestAdmitsRatioTwoCutPencilDecomposition : Prop :=
  ∀ g : BombieriTest,
    ∃ cells : List BombieriTest,
      cells.sum = g ∧
        (∀ f ∈ cells, BombieriRatioTwoCell f) ∧
          BombieriCellChainPencilNonnegative cells

/-- The partition-selected condition is exactly enough for global Bombieri
quadratic nonnegativity, hence exactly RH.  In particular, neither one fixed
partition scheme nor contraction for every possible cell list is required. -/
theorem riemannHypothesis_iff_everyTest_admits_contractingRatioTwoDecomposition
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔
      BombieriEveryTestAdmitsContractingRatioTwoDecomposition := by
  constructor
  · intro hRH g
    obtain ⟨cells, hsum, hcells⟩ := exists_ratioTwoCell_decomposition g
    refine ⟨cells, hsum, hcells, ?_⟩
    exact
      (riemannHypothesis_iff_everyRatioTwoCellChainContraction zeros).1 hRH
        cells hcells
  · intro hselected
    apply (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).2
    intro g
    obtain ⟨cells, hsum, hcells, hchain⟩ := hselected g
    rw [← hsum]
    exact bombieriFunctional_quadratic_re_nonneg_of_cellChain cells hcells hchain

/-- Equivalently, it is enough to choose one ratio-two partition per test for
which every ordered head--suffix pencil is nonnegative.  Unlike the universal
two-block criterion, these blocks may be correlated pieces of the same test. -/
theorem riemannHypothesis_iff_everyTest_admits_ratioTwoCutPencilDecomposition
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔
      BombieriEveryTestAdmitsRatioTwoCutPencilDecomposition := by
  constructor
  · intro hRH g
    obtain ⟨cells, hsum, hcells⟩ := exists_ratioTwoCell_decomposition g
    refine ⟨cells, hsum, hcells, ?_⟩
    apply
      (bombieriCellChainContraction_iff_cutPencilNonnegative cells hcells).1
    exact
      (riemannHypothesis_iff_everyRatioTwoCellChainContraction zeros).1 hRH
        cells hcells
  · intro hpencils
    apply
      (riemannHypothesis_iff_everyTest_admits_contractingRatioTwoDecomposition
        zeros).2
    intro g
    obtain ⟨cells, hsum, hcells, hpencil⟩ := hpencils g
    exact ⟨cells, hsum, hcells,
      (bombieriCellChainContraction_iff_cutPencilNonnegative
        cells hcells).2 hpencil⟩

/-- Every test has a ratio-two decomposition ordered by the concrete
left-support key.  This geometric sorting is unconditional; no positivity or
chain hypothesis is used. -/
theorem exists_leftOrdered_ratioTwoCell_decomposition (g : BombieriTest) :
    ∃ cells : List BombieriTest,
      cells.sum = g ∧
        (∀ f ∈ cells, BombieriRatioTwoCell f) ∧
          cells.Pairwise
            (fun f h ↦ bombieriCellLeftSupportKey f ≤
              bombieriCellLeftSupportKey h) := by
  classical
  obtain ⟨cells, hsum, hcells⟩ := exists_ratioTwoCell_decomposition g
  let ordered := cells.mergeSort
    (fun f h ↦ bombieriCellLeftSupportKey f ≤ bombieriCellLeftSupportKey h)
  have hperm : List.Perm ordered cells := by
    exact List.mergeSort_perm _ _
  have hordered :
      ordered.Pairwise
        (fun f h ↦ bombieriCellLeftSupportKey f ≤
          bombieriCellLeftSupportKey h) := by
    have hbool :=
      cells.pairwise_mergeSort
        (le := fun f h ↦ decide
          (bombieriCellLeftSupportKey f ≤ bombieriCellLeftSupportKey h))
        (fun f h k hfh hhk ↦ by
          simpa only [decide_eq_true_eq] using
            le_trans (of_decide_eq_true hfh) (of_decide_eq_true hhk))
        (fun f h ↦ by
          simpa only [Bool.or_eq_true, decide_eq_true_eq] using
            le_total (bombieriCellLeftSupportKey f)
              (bombieriCellLeftSupportKey h))
    change
      (cells.mergeSort
        (fun f h ↦ decide
          (bombieriCellLeftSupportKey f ≤ bombieriCellLeftSupportKey h))).Pairwise
        (fun f h ↦ bombieriCellLeftSupportKey f ≤
          bombieriCellLeftSupportKey h)
    exact hbool.imp (fun h ↦ of_decide_eq_true h)
  refine ⟨ordered, ?_, ?_, hordered⟩
  · exact hperm.sum_eq.trans hsum
  · intro f hf
    exact hcells f (hperm.mem_iff.mp hf)

/-- Under RH, the unconditional left-ordered partition also satisfies the
recursive chain inequalities.  Thus RH enters only at the algebraic
head--whole-tail step, not in constructing or ordering the cells. -/
theorem exists_leftOrdered_contractingRatioTwoDecomposition_of_riemannHypothesis
    (zeros : ZetaZeroEnumeration) (hRH : RiemannHypothesis)
    (g : BombieriTest) :
    BombieriAdmitsLeftOrderedContractingRatioTwoDecomposition g := by
  obtain ⟨cells, hsum, hcells, hordered⟩ :=
    exists_leftOrdered_ratioTwoCell_decomposition g
  refine ⟨cells, hsum, hcells, hordered, ?_⟩
  exact
      (riemannHypothesis_iff_everyRatioTwoCellChainContraction zeros).1 hRH
        cells hcells

/-- Even after imposing the concrete left-support order, existence of one
successful ratio-two chain per test remains exactly RH.  Thus ordering is a
legitimate place to exploit geometry, but sorting alone cannot manufacture
the missing contractions. -/
theorem
    riemannHypothesis_iff_everyTest_admits_leftOrderedContractingRatioTwoDecomposition
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔
      BombieriEveryTestAdmitsLeftOrderedContractingRatioTwoDecomposition := by
  constructor
  · intro hRH g
    exact
      exists_leftOrdered_contractingRatioTwoDecomposition_of_riemannHypothesis
        zeros hRH g
  · intro hordered
    apply
      (riemannHypothesis_iff_everyTest_admits_contractingRatioTwoDecomposition
        zeros).2
    intro g
    obtain ⟨cells, hsum, hcells, _horder, hchain⟩ := hordered g
    exact ⟨cells, hsum, hcells, hchain⟩

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
