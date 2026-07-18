import ArithmeticHodge.Analysis.FiniteIntervalWeightedGramTraceStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural

set_option autoImplicit false

open Matrix MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderTraceStructural

open FiniteIntervalWeightedGramTraceStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural

noncomputable section

/-!
# Trace form of the retained P024 even remainder Gram

The six-row even remainder cost is one interval integral of a finite sum of
nonnegative row energies.  This is the scalar interface used by a structural
pointwise majorant.
-/

/-- The retained P024 even remainder Gram is the generic interval weighted
Gram of its six shifted remainder rows. -/
theorem retainedP024SelectorWholeEvenShiftedRemainderGram_eq_intervalWeightedGram :
    retainedP024SelectorWholeEvenShiftedRemainderGram =
      finiteIntervalWeightedGram (-1) 1
        factorTwoIntrinsicElevenRetainedEvenWeight
        retainedP024SelectorWholeEvenShiftedRemainder := by
  ext i j
  rw [retainedP024SelectorWholeEvenShiftedRemainderGram_apply]
  rfl

/-- Every diagonal even remainder-energy integrand is
interval-integrable. -/
theorem intervalIntegrable_retainedP024SelectorWholeEvenShiftedRemainderEnergy
    (i : Fin 3 ⊕ Fin 3) :
    IntervalIntegrable
      (finiteIntervalWeightedRowEnergy
        factorTwoIntrinsicElevenRetainedEvenWeight
        retainedP024SelectorWholeEvenShiftedRemainder i)
      volume (-1) 1 := by
  unfold finiteIntervalWeightedRowEnergy
  simpa only [pow_two] using
    intervalIntegrable_retainedP024SelectorWholeEvenShiftedRemainderCross i i

/-- Trace of the six-row even remainder Gram as one summed-energy
integral. -/
theorem retainedP024SelectorWholeEvenShiftedRemainderGram_trace_eq_integral_sum :
    retainedP024SelectorWholeEvenShiftedRemainderGram.trace =
      ∫ x : Real in -1..1, ∑ i : Fin 3 ⊕ Fin 3,
        finiteIntervalWeightedRowEnergy
          factorTwoIntrinsicElevenRetainedEvenWeight
          retainedP024SelectorWholeEvenShiftedRemainder i x := by
  rw [retainedP024SelectorWholeEvenShiftedRemainderGram_eq_intervalWeightedGram]
  exact finiteIntervalWeightedGram_trace_eq_integral_sum
    (-1) 1 factorTwoIntrinsicElevenRetainedEvenWeight
    retainedP024SelectorWholeEvenShiftedRemainder
    intervalIntegrable_retainedP024SelectorWholeEvenShiftedRemainderEnergy

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderTraceStructural
