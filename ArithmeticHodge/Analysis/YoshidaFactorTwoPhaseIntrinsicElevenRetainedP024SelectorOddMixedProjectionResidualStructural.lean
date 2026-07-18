import ArithmeticHodge.Analysis.FiniteWeightedSelectorProjectionResidualStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionStructural

set_option autoImplicit false

open Matrix MeasureTheory Polynomial Real Set
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionResidualStructural

open FiniteBilinearGramProjectionStructural
open FiniteIntervalWeightedGramTraceStructural
open FiniteWeightedSelectorProjection
open FiniteWeightedSelectorProjectionResidualStructural
open ShiftedLegendreLogEnergyOrthogonalProjection
open YoshidaFactorTwoPhaseIntrinsicElevenConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedConstrainedWeightedDualStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorPoleRemainderStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorQuotientStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedSelectorHomogeneityStructural

noncomputable section

/-!
# Residual-energy form of the retained P024 odd projection defect

The comparison family here is the weighted family: eleven odd shifted
Legendre rows followed by the three exact prime-step rows.  Contracting its
fixed rational coefficient matrix before integration leaves only three
residual functions.
-/

/-- The three coefficient-contracted residual rows behind the retained P024
odd mixed-projection certificate. -/
def retainedP024OddMixedProjectionCertificateResidualRow :
    Fin 3 -> Real -> Real :=
  finiteProjectionResidualRow
    retainedP024SelectorAlternatingShiftedRemainder
    (retainedP024OddMixedProjectionWeightedRow
      retainedP024OddMixedProjectionDegree)
    retainedP024OddMixedProjectionCoefficient

/-- The odd projection defect is exactly the weighted Gram of the three
contracted residual rows. -/
theorem retainedP024OddMixedProjectionDefect_eq_residualGram :
    retainedP024SelectorAlternatingShiftedRemainderGram -
        retainedP024OddMixedProjectionCertificateGram =
      finiteIntervalWeightedGram (-1) 1
        factorTwoIntrinsicElevenRetainedOddWeight
        retainedP024OddMixedProjectionCertificateResidualRow := by
  let W := factorTwoIntrinsicElevenRetainedOddWeight
  let F := retainedP024SelectorAlternatingShiftedRemainder
  let G := retainedP024OddMixedProjectionWeightedRow
    retainedP024OddMixedProjectionDegree
  let C := retainedP024OddMixedProjectionCoefficient
  have h := finiteWeightedGram_projectionResidualRow_eq
    W F G
    (fun x hx => factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
    retainedP024SelectorAlternatingShiftedRemainder_div_sqrt_memLp_two
    (retainedP024OddMixedProjectionWeightedRow_div_sqrt_memLp_two
      retainedP024OddMixedProjectionDegree)
    C
  calc
    retainedP024SelectorAlternatingShiftedRemainderGram -
        retainedP024OddMixedProjectionCertificateGram =
      finiteWeightedGram W
        retainedP024OddMixedProjectionCertificateResidualRow := by
      symm
      simpa [W, F, G, C,
        retainedP024OddMixedProjectionCertificateResidualRow,
        retainedP024SelectorAlternatingShiftedRemainderGram,
        retainedP024OddMixedProjectionCertificateGram,
        retainedP024OddMixedProjectionLowerGram,
        retainedP024OddMixedProjectionCrossGram,
        retainedP024OddMixedProjectionModeGram,
        finiteWeightedGram] using h
    _ = finiteIntervalWeightedGram (-1) 1 W
        retainedP024OddMixedProjectionCertificateResidualRow :=
      finiteWeightedGram_eq_finiteIntervalWeightedGram W _

/-- Each normalized contracted residual row remains in the retained odd
weighted `L2` space. -/
theorem retainedP024OddMixedProjectionCertificateResidualRow_div_sqrt_memLp_two
    (i : Fin 3) :
    MemLp (fun x =>
      retainedP024OddMixedProjectionCertificateResidualRow i x /
        Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x)) 2
      (volume.restrict (Ioc (-1 : Real) 1)) := by
  let W := factorTwoIntrinsicElevenRetainedOddWeight
  let G := retainedP024OddMixedProjectionWeightedRow
    retainedP024OddMixedProjectionDegree
  let C := retainedP024OddMixedProjectionCoefficient
  have hsum : MemLp (fun x => ∑ k,
      C i k * (G k x / Real.sqrt (W x))) 2
      (volume.restrict (Ioc (-1 : Real) 1)) := by
    simpa only using memLp_finset_sum Finset.univ (fun k _hk =>
      (retainedP024OddMixedProjectionWeightedRow_div_sqrt_memLp_two
        retainedP024OddMixedProjectionDegree k).const_mul (C i k))
  have hsub :=
    (retainedP024SelectorAlternatingShiftedRemainder_div_sqrt_memLp_two i).sub
      hsum
  apply (memLp_congr_ae (μ := volume.restrict (Ioc (-1 : Real) 1)) ?_).mpr hsub
  filter_upwards with x
  simp only [retainedP024OddMixedProjectionCertificateResidualRow,
    finiteProjectionResidualRow, Pi.sub_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, W, G, C]
  rw [sub_div]
  rw [Finset.sum_div]
  apply congrArg (fun y =>
    retainedP024SelectorAlternatingShiftedRemainder i x /
      Real.sqrt (factorTwoIntrinsicElevenRetainedOddWeight x) - y)
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- Every diagonal residual-energy integrand is interval-integrable. -/
theorem intervalIntegrable_retainedP024OddMixedProjectionCertificateResidualEnergy
    (i : Fin 3) :
    IntervalIntegrable
      (finiteIntervalWeightedRowEnergy
        factorTwoIntrinsicElevenRetainedOddWeight
        retainedP024OddMixedProjectionCertificateResidualRow i)
      volume (-1) 1 := by
  have h := intervalIntegrable_selectorCross_of_memLp
    factorTwoIntrinsicElevenRetainedOddWeight
    (retainedP024OddMixedProjectionCertificateResidualRow i)
    (retainedP024OddMixedProjectionCertificateResidualRow i)
    0 0
    (fun x hx => factorTwoIntrinsicElevenRetainedOddWeight_pos_on_Icc hx)
    (by
      simpa [factorTwoIntrinsicElevenSelectorResidual,
        centeredPolynomialLift] using
        retainedP024OddMixedProjectionCertificateResidualRow_div_sqrt_memLp_two i)
    (by
      simpa [factorTwoIntrinsicElevenSelectorResidual,
        centeredPolynomialLift] using
        retainedP024OddMixedProjectionCertificateResidualRow_div_sqrt_memLp_two i)
  unfold finiteIntervalWeightedRowEnergy
  simpa [factorTwoIntrinsicElevenSelectorResidual,
    centeredPolynomialLift, pow_two] using h

/-- Trace form of the P024 odd projection defect: one integral of the summed
energy of three residual rows. -/
theorem retainedP024OddMixedProjectionDefect_trace_eq_integral_sum :
    (retainedP024SelectorAlternatingShiftedRemainderGram -
        retainedP024OddMixedProjectionCertificateGram).trace =
      ∫ x : Real in -1..1, ∑ i : Fin 3,
        finiteIntervalWeightedRowEnergy
          factorTwoIntrinsicElevenRetainedOddWeight
          retainedP024OddMixedProjectionCertificateResidualRow i x := by
  rw [retainedP024OddMixedProjectionDefect_eq_residualGram]
  exact finiteIntervalWeightedGram_trace_eq_integral_sum
    (-1) 1 factorTwoIntrinsicElevenRetainedOddWeight
    retainedP024OddMixedProjectionCertificateResidualRow
    intervalIntegrable_retainedP024OddMixedProjectionCertificateResidualEnergy

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionResidualStructural
