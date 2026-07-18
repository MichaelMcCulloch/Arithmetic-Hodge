import ArithmeticHodge.Analysis.MultiplicativeWeilRatioTwoPartitionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCriterionClosure

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.MultiplicativeWeil

noncomputable section

/-!
# Cell-chain contraction is the terminal Bombieri criterion

The recursive head-against-whole-tail contraction introduced for finite
ratio-two cell assembly is sound, but it is not a smaller intermediate lemma
on the route to RH.  Once the existing ratio-two partition and local cell
positivity theorems are in place, either a universal two-block contraction or
the corresponding assertion for every ratio-two cell list is equivalent to
the Riemann hypothesis itself.

Consequently, proving one of the conditions below still requires genuinely
global input.  Same-seed adjacent positivity or independent pairwise
principal-block estimates cannot discharge it merely by formal assembly.
-/

/-- The support-free two-block Cauchy--Schwarz inequality for the concrete
Bombieri form. -/
def BombieriUniversalTwoBlockContraction : Prop :=
  ∀ f g : BombieriTest,
    Complex.normSq (bombieriTwoBlockGlobalCrossSymbol f g) ≤
      (bombieriFunctional (bombieriQuadraticTest f)).re *
        (bombieriFunctional (bombieriQuadraticTest g)).re

/-- The exact whole-tail condition needed after a ratio-two partition. -/
def BombieriEveryRatioTwoCellChainContraction : Prop :=
  ∀ cells : List BombieriTest,
    (∀ g ∈ cells, BombieriRatioTwoCell g) →
      BombieriCellChainContraction cells

/-- A universal two-block contraction supplies every recursive whole-tail
contraction, independently of how the cells were chosen. -/
theorem bombieriCellChainContraction_of_universalTwoBlock
    (h : BombieriUniversalTwoBlockContraction)
    (cells : List BombieriTest) :
    BombieriCellChainContraction cells := by
  induction cells with
  | nil => trivial
  | cons f tail ih =>
      cases tail with
      | nil => trivial
      | cons g rest =>
          exact ⟨ih, h f (g :: rest).sum⟩

/-- Once finite ratio-two partitioning and local cell positivity are in
place, the universal head--whole-tail contraction is exactly RH. -/
theorem riemannHypothesis_iff_universalTwoBlockContraction
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔ BombieriUniversalTwoBlockContraction := by
  constructor
  · intro hRH
    have hQ : ∀ g : BombieriTest,
        0 ≤ (bombieriFunctional (bombieriQuadraticTest g)).re :=
      (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).1 hRH
    intro f g
    apply (bombieriFunctional_twoBlock_nonneg_iff
      f g (hQ f) (hQ g)).1
    intro c
    exact hQ (f + c • g)
  · intro hcontract
    apply (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).2
    intro g
    obtain ⟨cells, hsum, hcells⟩ := exists_ratioTwoCell_decomposition g
    rw [← hsum]
    exact bombieriFunctional_quadratic_re_nonneg_of_cellChain cells hcells
      (bombieriCellChainContraction_of_universalTwoBlock hcontract cells)

/-- Equivalently, RH says that every finite ratio-two cell list satisfies the
recursive head-against-whole-tail Schur inequality. -/
theorem riemannHypothesis_iff_everyRatioTwoCellChainContraction
    (zeros : ZetaZeroEnumeration) :
    RiemannHypothesis ↔ BombieriEveryRatioTwoCellChainContraction := by
  constructor
  · intro hRH cells _hcells
    have huniversal : BombieriUniversalTwoBlockContraction :=
      (riemannHypothesis_iff_universalTwoBlockContraction zeros).1 hRH
    exact bombieriCellChainContraction_of_universalTwoBlock huniversal cells
  · intro hchain
    apply (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).2
    intro g
    obtain ⟨cells, hsum, hcells⟩ := exists_ratioTwoCell_decomposition g
    rw [← hsum]
    exact bombieriFunctional_quadratic_re_nonneg_of_cellChain cells hcells
      (hchain cells hcells)

end

end ArithmeticHodge.Analysis.MultiplicativeWeil
