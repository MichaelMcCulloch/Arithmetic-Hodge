import ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerResidualParentMaskStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilQuarterLogLatticeCoherentFejerDecompositionStructural
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCriterionClosure

set_option autoImplicit false

open Complex Finset Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerAbsorptionCriterionStructural

noncomputable section

open MultiplicativeWeil
open MultiplicativeWeilCoherentFejerResidualParentMaskStructural
open MultiplicativeWeilFejerLinearResidualStructural
open MultiplicativeWeilFejerLocalizationStructural
open MultiplicativeWeilFejerResidualCrossTestStructural
open MultiplicativeWeilQuarterLogLatticeCoherentFejerDecompositionStructural
open MultiplicativeWeilQuarterLogLatticeFejerAssemblyStructural

/-!
# Universal coherent Fejer absorption is not a reduction of RH

This module is an obstruction diagnostic.  It packages the unqualified
parent-mask absorption inequality and proves that universal validity of that
inequality is equivalent to the Riemann hypothesis.  The equivalence does not
prove either proposition; it shows that the universal absorption statement
cannot serve as a mathematically weaker intermediate target.
-/

/-- Universal unqualified absorption for every finite coherent block.  The
inequality is literally the right side of
`bombieriQuadraticRealValue_paddedIntegerBlock_sum_nonnegative_iff_parentMask_absorption`;
no support geometry, positivity, or partition assumptions are added. -/
def UniversalCoherentFejerParentMaskAbsorption : Prop :=
  ∀ (parent : BombieriTest)
    (A : ℤ → BombieriTest) (eta : ℤ → ℝ → ℝ)
    (lo : ℤ) (n : ℕ),
    (∀ k : ℤ, ∀ x : ℝ,
      A k x = ((eta k x : ℝ) : ℂ) * parent x) →
    -bombieriCyclicFejerThree (finRotate (n + 2))
        (paddedIntegerBlock A lo n) ≤
      (bombieriFunctional
        (bombieriWeightedLinearLagCrossTest
          bombieriFejerThreeResidualLagWeight
          (List.ofFn (integerBlock A lo n)))).re

/-- Obstruction diagnostic: the unqualified universal absorption target is
exactly RH.  Absorption implies Bombieri nonnegativity through the arbitrary
coherent decomposition; RH implies absorption by applying Bombieri
nonnegativity to each padded sum.  This equivalence supplies no proof of RH
or of universal absorption. -/
theorem universalCoherentFejerParentMaskAbsorption_iff_riemannHypothesis
    (zeros : ZetaZeroEnumeration) :
    UniversalCoherentFejerParentMaskAbsorption ↔ RiemannHypothesis := by
  constructor
  · intro habsorb
    apply (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).2
    intro g
    obtain ⟨A, eta, lo, n, b, _hn, hb, _houtside, _hsupport,
      hcommon, _hsmooth, _hnonneg, _hetaSum, _hdisjoint, hbsum,
      _hwindows, _hfejer, _hexact⟩ :=
      exists_padded_coherent_quarterLogLattice_fejer_decomposition g
    have habs := habsorb g A eta lo n hcommon
    have hnonneg : 0 ≤ bombieriQuadraticRealValue
        (∑ i, paddedIntegerBlock A lo n i) :=
      (bombieriQuadraticRealValue_paddedIntegerBlock_sum_nonnegative_iff_parentMask_absorption
        g A eta lo n hcommon).2 habs
    have hsum : (∑ i, paddedIntegerBlock A lo n i) = g := by
      rw [← hb]
      exact hbsum
    simpa only [bombieriQuadraticRealValue, hsum] using hnonneg
  · intro hRH parent A eta lo n hcommon
    have hnonneg : 0 ≤ bombieriQuadraticRealValue
        (∑ i, paddedIntegerBlock A lo n i) := by
      exact (riemannHypothesis_iff_bombieriQuadratic_re_nonnegative zeros).1
        hRH (∑ i, paddedIntegerBlock A lo n i)
    exact
      (bombieriQuadraticRealValue_paddedIntegerBlock_sum_nonnegative_iff_parentMask_absorption
        parent A eta lo n hcommon).1 hnonneg

end

end ArithmeticHodge.Analysis.MultiplicativeWeilCoherentFejerAbsorptionCriterionStructural
