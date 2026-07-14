import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanOddMatrix
import ArithmeticHodge.Analysis.YoshidaOddGramPosDef

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanOddPositive

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaDiagonalMomentEnclosures
open YoshidaCoercivityNumerics
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaOddGramPrefix
open YoshidaOddIntervalCertificate
open YoshidaOddMomentTargets
open YoshidaOddRealSpaceAssembly
open YoshidaSineMomentEnclosures
open YoshidaWeightedTailBounds

/-!
# Positive definiteness of the concrete odd clean block

The concrete endpoint clean matrix is the positive scalar rescaling of the
real odd moment matrix whose interval Schur certificate is already complete.
-/

/-- The concrete odd clean matrix is exactly the odd moment matrix divided by
the positive endpoint scale. -/
theorem factorTwoConcreteOddCleanMatrix_eq_scaled_oddMomentFullGram :
    factorTwoConcreteOddCleanMatrix =
      yoshidaA⁻¹ •
        oddMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment := by
  ext i j
  have hentry := congrArg Complex.re (clippedOddFullMomentBridge i j)
  simp only [clippedOddFullGram, yoshidaClippedOddGram,
    Complex.ofReal_re] at hentry
  have hentry' :
      (yoshidaClippedLocalCriticalForm yoshidaA yoshidaA_pos
        (yoshidaClippedOddLowMode yoshidaA i)
        (yoshidaClippedOddLowMode yoshidaA j)).re =
          oddMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment i j := by
    simpa only [yoshidaHalfLength, yoshidaLength, yoshidaA] using hentry
  simp only [factorTwoConcreteOddCleanMatrix, smul_apply, smul_eq_mul]
  rw [hentry']
  ring

private theorem oddMomentFullGram_posDef :
    (oddMomentFullGram yoshidaSineMoment
      yoshidaDiagonalMoment).PosDef :=
  oddMomentFullGram_posDef_of_intervalPivots
    yoshidaSineMoment yoshidaDiagonalMoment
    yoshidaOddSineIntervals yoshidaOddDiagonalIntervals
    sineTargetEnclosures_from_series192
    diagonalTargetEnclosures_from_certificate
    yoshidaOddTarget_intervalPivots

/-- The fully concrete ten-dimensional odd clean matrix is positive
definite. -/
theorem factorTwoConcreteOddCleanMatrix_posDef :
    factorTwoConcreteOddCleanMatrix.PosDef := by
  rw [factorTwoConcreteOddCleanMatrix_eq_scaled_oddMomentFullGram]
  exact oddMomentFullGram_posDef.smul (inv_pos.mpr yoshidaA_pos)

/-- Positive semidefiniteness of the concrete odd clean matrix. -/
theorem factorTwoConcreteOddCleanMatrix_posSemidef :
    factorTwoConcreteOddCleanMatrix.PosSemidef :=
  factorTwoConcreteOddCleanMatrix_posDef.posSemidef

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanOddPositive
