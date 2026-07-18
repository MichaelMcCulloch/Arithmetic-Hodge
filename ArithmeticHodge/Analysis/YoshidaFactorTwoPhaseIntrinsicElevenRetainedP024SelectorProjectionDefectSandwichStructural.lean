import ArithmeticHodge.Analysis.SignedBlockGramSandwichStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorProjectionDefectSandwichStructural

open SignedBlockGramSandwichStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorOddMixedProjectionStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorRemainderGramStructural
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorSOSStructural

noncomputable section

/-!
# Projection-defect sandwich for the retained P024 selector

The six-row even remainder Gram is paid for by one scalar trace reserve.  In
the alternating channel, the existing mixed Legendre/prime-step lower Gram is
retained exactly and only its positive projection defect is paid for by a
second scalar trace reserve.
-/

/-- The retained P024 asymmetric SOS Gram is exactly the generic signed-block
Gram built from its nonquotient and remainder pieces. -/
theorem retainedP024SelectorAsymmetricSOSGram_eq_exactSignedBlockGram :
    retainedP024SelectorAsymmetricSOSGram =
      exactSignedBlockGram
        retainedP024SharpLowSOSGram
        retainedP024SelectorWholeEvenNonquotientGram
        retainedP024SelectorWholeEvenShiftedRemainderGram
        retainedP024SelectorAlternatingNonquotientGram
        retainedP024SelectorAlternatingShiftedRemainderGram := by
  rw [retainedP024SelectorAsymmetricSOSGram_eq_nonquotient_remainders]
  unfold exactSignedBlockGram signedDiagonalLift
    retainedP024AlternatingSignedLift
  rfl

/-- Fixed inverse-weight-free matrix after replacing the even remainder and
the odd mixed-projection defect by scalar identity reserves. -/
def retainedP024SelectorScalarTraceProjectionDefectSandwichGram
    (gammaEven gammaOddDefect : ℝ) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℝ :=
  scalarTraceProjectedDefectSignedBlockGramSandwich
    retainedP024SharpLowSOSGram
    retainedP024SelectorWholeEvenNonquotientGram
    retainedP024SelectorAlternatingNonquotientGram
    retainedP024OddMixedProjectionCertificateGram
    gammaEven gammaOddDefect

/-- The retained P024 closure is reduced to two scalar trace bounds and
positive definiteness of one fixed inverse-weight-free `6 x 6` matrix. -/
theorem retainedP024SelectorAsymmetricSOSGram_posDef_of_projectionDefectTraces
    (gammaEven gammaOddDefect : ℝ)
    (hEvenTrace :
      retainedP024SelectorWholeEvenShiftedRemainderGram.trace ≤ gammaEven)
    (hOddDefectTrace :
      (retainedP024SelectorAlternatingShiftedRemainderGram -
        retainedP024OddMixedProjectionCertificateGram).trace ≤
          gammaOddDefect)
    (hSandwich :
      (retainedP024SelectorScalarTraceProjectionDefectSandwichGram
        gammaEven gammaOddDefect).PosDef) :
    retainedP024SelectorAsymmetricSOSGram.PosDef := by
  rw [retainedP024SelectorAsymmetricSOSGram_eq_exactSignedBlockGram]
  apply exactSignedBlockGram_posDef_of_scalarTraceProjectedDefectSandwich
    retainedP024SharpLowSOSGram
    retainedP024SelectorWholeEvenNonquotientGram
    retainedP024SelectorWholeEvenShiftedRemainderGram
    retainedP024SelectorAlternatingNonquotientGram
    retainedP024SelectorAlternatingShiftedRemainderGram
    retainedP024OddMixedProjectionCertificateGram
    gammaEven gammaOddDefect
  · exact retainedP024SelectorWholeEvenShiftedRemainderGram_posSemidef
  · exact retainedP024OddMixedProjectionCertificateGram_le
  · exact hEvenTrace
  · exact hOddDefectTrace
  · exact hSandwich

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024SelectorProjectionDefectSandwichStructural
