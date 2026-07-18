import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionResidualStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorProjectionDefectSandwichStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderTraceStructural

set_option autoImplicit false

open Matrix Real
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorResidualEnergySandwichStructural

open FiniteIntervalWeightedGramTraceStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionResidualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorProjectionDefectSandwichStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderTraceStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural

noncomputable section

/-!
# Residual-energy handoff for the retained P024 selector

The exact fixed Gram is positive definite once two scalar energy integrals
fit inside reserves that preserve positivity of one inverse-weight-free
`6 x 6` sandwich matrix.
-/

/-- Exact P024 positivity from structural even and odd residual-energy
bounds. -/
theorem retainedP024SelectorAsymmetricSOSGram_posDef_of_residualEnergyBounds
    (gammaEven gammaOddDefect : Real)
    (hEvenEnergy :
      (∫ x : Real in -1..1, ∑ i : Fin 3 ⊕ Fin 3,
        finiteIntervalWeightedRowEnergy
          factorTwoIntrinsicElevenRetainedEvenWeight
          retainedP024SelectorWholeEvenShiftedRemainder i x) ≤ gammaEven)
    (hOddDefectEnergy :
      (∫ x : Real in -1..1, ∑ i : Fin 3,
        finiteIntervalWeightedRowEnergy
          factorTwoIntrinsicElevenRetainedOddWeight
          retainedP024OddMixedProjectionCertificateResidualRow i x) ≤
        gammaOddDefect)
    (hSandwich :
      (retainedP024SelectorScalarTraceProjectionDefectSandwichGram
        gammaEven gammaOddDefect).PosDef) :
    retainedP024SelectorAsymmetricSOSGram.PosDef := by
  apply retainedP024SelectorAsymmetricSOSGram_posDef_of_projectionDefectTraces
    gammaEven gammaOddDefect
  · rw [retainedP024SelectorWholeEvenShiftedRemainderGram_trace_eq_integral_sum]
    exact hEvenEnergy
  · rw [retainedP024OddMixedProjectionDefect_trace_eq_integral_sum]
    exact hOddDefectEnergy
  · exact hSandwich

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorResidualEnergySandwichStructural
