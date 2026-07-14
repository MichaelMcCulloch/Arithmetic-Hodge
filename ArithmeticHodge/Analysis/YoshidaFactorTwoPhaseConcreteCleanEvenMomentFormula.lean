import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
import ArithmeticHodge.Analysis.YoshidaEvenCriticalCrossBridge
import ArithmeticHodge.Analysis.YoshidaClippedEvenMomentBridge

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanEvenMomentFormula

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaClippedEvenMomentBridge
open YoshidaCoercivityNumerics
open YoshidaEvenCriticalCrossBridge
open YoshidaEvenDistributionReduction
open YoshidaEvenIntervalCertificate
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaOddGramPrefix
open YoshidaWeightedTailBounds

/-!
# Exact moment entries for the endpoint-adapted even clean block

Endpoint adaptation adds frequency `200` to the certified canonical range
`0, ..., 199`.  This module exposes the resulting clean entry as the exact
four-term pullback of the Section-6 moment Gram.  It makes the two new scalar
inputs `S_200` and `D_200` explicit without asserting numerical enclosures.
-/

/-- The production local critical pairing equals the Section-6 moment entry
for every pair of canonical even frequencies, including frequency `200`. -/
theorem yoshidaClippedLocalCriticalForm_unifiedEven_eq_evenMomentGram
    (n m : ℕ) :
    yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m) =
      (evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment n m : ℂ) := by
  change yoshidaClippedLocalCriticalPairing yoshidaA yoshidaA_pos
      (clippedEvenUnifiedMode n) (clippedEvenUnifiedMode m) = _
  have h := yoshidaClippedLocalCriticalPairing_even_eq_admissible
    clippedEvenCriticalCrossDistributionBridge n m
  rw [clippedEvenAdmissibleRealSpaceGram_eq_evenMomentGram] at h
  simpa only [yoshidaHalfLength, yoshidaLength, yoshidaA] using h

/-- The exact real entry obtained by pulling the canonical `0, ..., 200`
moment Gram back along the endpoint-adapted basis. -/
def factorTwoConcreteAdaptedEvenCleanMomentEntry
    (i j : YoshidaEvenIndex) : ℝ :=
  (evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment i.1 j.1 -
      endpointEvenLowTraceRatio j *
        evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment i.1 200 -
      endpointEvenLowTraceRatio i *
        evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment 200 j.1 +
      endpointEvenLowTraceRatio i * endpointEvenLowTraceRatio j *
        evenMomentGram yoshidaSineMoment yoshidaDiagonalMoment 200 200) /
    yoshidaA

/-- Every concrete endpoint-adapted even clean entry is its explicit
four-term Section-6 moment pullback. -/
theorem factorTwoConcreteAdaptedEvenCleanMatrix_apply
    (i j : YoshidaEvenIndex) :
    factorTwoConcreteAdaptedEvenCleanMatrix i j =
      factorTwoConcreteAdaptedEvenCleanMomentEntry i j := by
  let li := clippedEvenUnifiedMode i.1
  let lj := clippedEvenUnifiedMode j.1
  let h := clippedEvenUnifiedMode 200
  have hli : yoshidaClippedEvenLowMode yoshidaA i = li := by
    simpa only [li, yoshidaHalfLength, yoshidaLength, yoshidaA] using
      (clippedEvenUnifiedMode_eq_lowMode i).symm
  have hlj : yoshidaClippedEvenLowMode yoshidaA j = lj := by
    simpa only [lj, yoshidaHalfLength, yoshidaLength, yoshidaA] using
      (clippedEvenUnifiedMode_eq_lowMode j).symm
  have htop : yoshidaClippedEvenMode yoshidaA 200 = h := by
    simp only [h, clippedEvenUnifiedMode,
      if_neg (by norm_num : (200 : ℕ) ≠ 0),
      yoshidaHalfLength, yoshidaLength, yoshidaA]
  change
    (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
      (yoshidaClippedEvenLowMode yoshidaA i -
        (endpointEvenLowTraceRatio i : ℂ) •
          yoshidaClippedEvenMode yoshidaA 200)
      (yoshidaClippedEvenLowMode yoshidaA j -
        (endpointEvenLowTraceRatio j : ℂ) •
          yoshidaClippedEvenMode yoshidaA 200)).re / yoshidaA = _
  rw [hli, hlj, htop]
  simp only [map_sub, map_smul, map_smulₛₗ, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [yoshidaClippedLocalCriticalForm_unifiedEven_eq_evenMomentGram,
    yoshidaClippedLocalCriticalForm_unifiedEven_eq_evenMomentGram,
    yoshidaClippedLocalCriticalForm_unifiedEven_eq_evenMomentGram,
    yoshidaClippedLocalCriticalForm_unifiedEven_eq_evenMomentGram]
  norm_num [Complex.mul_re]
  unfold factorTwoConcreteAdaptedEvenCleanMomentEntry
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanEvenMomentFormula
