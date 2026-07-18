import ArithmeticHodge.Analysis.FiniteIntervalWeightedGramTraceInteriorStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorResidualEnergySandwichStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedReciprocalMajorantStructural

set_option autoImplicit false

open Matrix MeasureTheory Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorReciprocalMajorantStructural

open FiniteIntervalWeightedGramTraceInteriorStructural
open FiniteIntervalWeightedGramTraceStructural
open YoshidaEndpointEvenAtanhReciprocalMajorant
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionResidualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorProjectionDefectSandwichStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderTraceStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorResidualEnergySandwichStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedReciprocalMajorantStructural

noncomputable section

/-!
# Polynomial reciprocal majorants for the retained P024 residual energies

The retained even and odd inverse weights are replaced on the open endpoint
interval by the fixed degree-six atanh reciprocal polynomial.  Endpoint
values are irrelevant to the volume integral.
-/

/-- Polynomial reciprocal majorant for the summed six-row even remainder
energy. -/
def retainedP024SelectorWholeEvenRemainderReciprocalMajorant
    (x : Real) : Real :=
  ∑ i : Fin 3 ⊕ Fin 3,
    (205 / 39 : Real) * atanhTailWeightReciprocalMajorant x *
      retainedP024SelectorWholeEvenShiftedRemainder i x ^ 2

/-- Polynomial reciprocal majorant for the summed three-row odd projection
defect energy. -/
def retainedP024OddMixedProjectionDefectReciprocalMajorant
    (x : Real) : Real :=
  ∑ i : Fin 3,
    (41 / 2 : Real) * atanhTailWeightReciprocalMajorant x *
      retainedP024OddMixedProjectionCertificateResidualRow i x ^ 2

/-- Interior pointwise domination of the full even remainder energy. -/
theorem retainedP024SelectorWholeEvenRemainderEnergy_le_reciprocalMajorant
    {x : Real} (hx : x ∈ Ioo (-1 : Real) 1) :
    (∑ i : Fin 3 ⊕ Fin 3,
      finiteIntervalWeightedRowEnergy
        factorTwoIntrinsicElevenRetainedEvenWeight
        retainedP024SelectorWholeEvenShiftedRemainder i x) ≤
      retainedP024SelectorWholeEvenRemainderReciprocalMajorant x := by
  unfold retainedP024SelectorWholeEvenRemainderReciprocalMajorant
  apply Finset.sum_le_sum
  intro i _hi
  exact sq_div_retainedEvenWeight_le_reciprocalMajorant_mul_sq
    (retainedP024SelectorWholeEvenShiftedRemainder i x) hx

/-- Interior pointwise domination of the odd mixed-projection defect
energy. -/
theorem retainedP024OddMixedProjectionDefectEnergy_le_reciprocalMajorant
    {x : Real} (hx : x ∈ Ioo (-1 : Real) 1) :
    (∑ i : Fin 3,
      finiteIntervalWeightedRowEnergy
        factorTwoIntrinsicElevenRetainedOddWeight
        retainedP024OddMixedProjectionCertificateResidualRow i x) ≤
      retainedP024OddMixedProjectionDefectReciprocalMajorant x := by
  unfold retainedP024OddMixedProjectionDefectReciprocalMajorant
  apply Finset.sum_le_sum
  intro i _hi
  exact sq_div_retainedOddWeight_le_reciprocalMajorant_mul_sq
    (retainedP024OddMixedProjectionCertificateResidualRow i x) hx

/-- The even remainder trace is bounded by the polynomial reciprocal
majorant integral. -/
theorem retainedP024SelectorWholeEvenShiftedRemainderGram_trace_le_reciprocalMajorant
    (hMajorant : IntervalIntegrable
      retainedP024SelectorWholeEvenRemainderReciprocalMajorant
      volume (-1) 1) :
    retainedP024SelectorWholeEvenShiftedRemainderGram.trace ≤
      ∫ x : Real in -1..1,
        retainedP024SelectorWholeEvenRemainderReciprocalMajorant x := by
  rw [retainedP024SelectorWholeEvenShiftedRemainderGram_eq_intervalWeightedGram]
  exact finiteIntervalWeightedGram_trace_le_integral_majorant_of_le_Ioo
    (-1) 1 (by norm_num)
    factorTwoIntrinsicElevenRetainedEvenWeight
    retainedP024SelectorWholeEvenShiftedRemainder
    retainedP024SelectorWholeEvenRemainderReciprocalMajorant
    intervalIntegrable_retainedP024SelectorWholeEvenShiftedRemainderEnergy
    hMajorant
    (fun x hx =>
      retainedP024SelectorWholeEvenRemainderEnergy_le_reciprocalMajorant hx)

/-- The odd projection-defect trace is bounded by its polynomial reciprocal
majorant integral. -/
theorem retainedP024OddMixedProjectionDefect_trace_le_reciprocalMajorant
    (hMajorant : IntervalIntegrable
      retainedP024OddMixedProjectionDefectReciprocalMajorant
      volume (-1) 1) :
    (retainedP024SelectorAlternatingShiftedRemainderGram -
        retainedP024OddMixedProjectionCertificateGram).trace ≤
      ∫ x : Real in -1..1,
        retainedP024OddMixedProjectionDefectReciprocalMajorant x := by
  rw [retainedP024OddMixedProjectionDefect_eq_residualGram]
  exact finiteIntervalWeightedGram_trace_le_integral_majorant_of_le_Ioo
    (-1) 1 (by norm_num)
    factorTwoIntrinsicElevenRetainedOddWeight
    retainedP024OddMixedProjectionCertificateResidualRow
    retainedP024OddMixedProjectionDefectReciprocalMajorant
    intervalIntegrable_retainedP024OddMixedProjectionCertificateResidualEnergy
    hMajorant
    (fun x hx =>
      retainedP024OddMixedProjectionDefectEnergy_le_reciprocalMajorant hx)

/-- Exact P024 positivity from rational ceilings on the two polynomial
reciprocal-majorant integrals and positivity of the resulting fixed
sandwich matrix. -/
theorem retainedP024SelectorAsymmetricSOSGram_posDef_of_reciprocalMajorantBounds
    (gammaEven gammaOddDefect : Real)
    (hEvenIntegrable : IntervalIntegrable
      retainedP024SelectorWholeEvenRemainderReciprocalMajorant
      volume (-1) 1)
    (hOddIntegrable : IntervalIntegrable
      retainedP024OddMixedProjectionDefectReciprocalMajorant
      volume (-1) 1)
    (hEvenBound :
      (∫ x : Real in -1..1,
        retainedP024SelectorWholeEvenRemainderReciprocalMajorant x) ≤
          gammaEven)
    (hOddBound :
      (∫ x : Real in -1..1,
        retainedP024OddMixedProjectionDefectReciprocalMajorant x) ≤
          gammaOddDefect)
    (hSandwich :
      (retainedP024SelectorScalarTraceProjectionDefectSandwichGram
        gammaEven gammaOddDefect).PosDef) :
    retainedP024SelectorAsymmetricSOSGram.PosDef := by
  apply retainedP024SelectorAsymmetricSOSGram_posDef_of_projectionDefectTraces
    gammaEven gammaOddDefect
  · exact (retainedP024SelectorWholeEvenShiftedRemainderGram_trace_le_reciprocalMajorant
      hEvenIntegrable).trans hEvenBound
  · exact (retainedP024OddMixedProjectionDefect_trace_le_reciprocalMajorant
      hOddIntegrable).trans hOddBound
  · exact hSandwich

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorReciprocalMajorantStructural
