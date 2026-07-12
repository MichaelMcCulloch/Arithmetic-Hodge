import ArithmeticHodge.Analysis.YoshidaEvenCorrectionReality
import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets

set_option autoImplicit false

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace ArithmeticHodge.Analysis.YoshidaEvenFiniteSchur

noncomputable section

open ArithmeticHodge.Analysis
open RationalIntervalSchur
open YoshidaEvenCorrectionReality
open YoshidaEvenCriticalCrossBridge
open YoshidaEvenIntervalCertificate
open YoshidaEvenMomentTargets
open YoshidaEvenTailLowFunctional
open YoshidaOddGramPrefix

/-- The real matrix underlying the actual even-tail Riesz correction. -/
def actualEvenTailCorrectionGramReal :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ :=
  fun i j ↦ (actualEvenTailCorrectionGram i j).re

theorem actualEvenTailCorrectionGramReal_isHermitian :
    actualEvenTailCorrectionGramReal.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [actualEvenTailCorrectionGramReal, star_trivial]
  have h := (Matrix.IsHermitian.ext_iff.mp
    actualEvenTailCorrectionGram_isHermitian) i j
  simpa only [Complex.star_def, Complex.conj_re] using
    congrArg Complex.re h

theorem complexOfRealMatrix_actualEvenTailCorrectionGramReal :
    complexOfRealMatrix actualEvenTailCorrectionGramReal =
      actualEvenTailCorrectionGram := by
  ext i j
  exact (actualEvenTailCorrectionGram_eq_ofReal i j).symm

/-- The actual real Schur complement of the canonical finite even block. -/
def actualEvenTailCorrectedRealGram :
    Matrix YoshidaEvenIndex YoshidaEvenIndex ℝ :=
  evenMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment -
    actualEvenTailCorrectionGramReal

theorem actualEvenTailCorrectedRealGram_isHermitian :
    actualEvenTailCorrectedRealGram.IsHermitian := by
  apply Matrix.IsHermitian.sub
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [evenMomentFullGram, star_trivial]
    exact evenMomentGram_comm _ _ _ _
  · exact actualEvenTailCorrectionGramReal_isHermitian

theorem actualEvenTailCorrectedRealGram_close
    (i j : YoshidaEvenIndex) :
    |actualEvenTailCorrectedRealGram i j -
        evenMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment i j| ≤
      (evenCorrectionRadius : ℝ) := by
  calc
    |actualEvenTailCorrectedRealGram i j -
        evenMomentFullGram yoshidaSineMoment yoshidaDiagonalMoment i j| =
        |-(actualEvenTailCorrectionGram i j).re| := by
      simp [actualEvenTailCorrectedRealGram,
        actualEvenTailCorrectionGramReal]
    _ = |(actualEvenTailCorrectionGram i j).re| := abs_neg _
    _ = ‖actualEvenTailCorrectionGram i j‖ := by
      rw [actualEvenTailCorrectionGram_eq_ofReal]
      simp
    _ ≤ (evenCorrectionRadius : ℝ) :=
      actualEvenTailCorrectionGram_norm_le_correctionRadius i j

theorem complexOfRealMatrix_actualEvenTailCorrectedRealGram :
    complexOfRealMatrix actualEvenTailCorrectedRealGram =
      clippedEvenFullGram - actualEvenTailCorrectionGram := by
  ext i j
  change (actualEvenTailCorrectedRealGram i j : ℂ) =
    clippedEvenFullGram i j - actualEvenTailCorrectionGram i j
  rw [clippedEvenFullMomentBridge i j]
  rw [actualEvenTailCorrectionGram_eq_ofReal]
  simp [actualEvenTailCorrectedRealGram,
    actualEvenTailCorrectionGramReal]

/-- The three exact finite certificates imply positivity of the actual
finite Schur complement, with no change to the certified `1/2000` radius. -/
theorem actualEvenTailCorrectedGram_posDef_of_certificates
    (hS : YoshidaEvenSineTargetEnclosures)
    (hD : YoshidaEvenDiagonalTargetEnclosures)
    (hP : YoshidaEvenFullTargetPivots) :
    (clippedEvenFullGram - actualEvenTailCorrectionGram).PosDef := by
  have hreal :
      (complexOfRealMatrix actualEvenTailCorrectedRealGram).PosDef :=
    correctedEvenComplexMatrix_posDef_of_intervalPivots
      evenCorrectionRadius yoshidaSineMoment yoshidaDiagonalMoment
      yoshidaEvenSineTargets yoshidaEvenDiagonalTargets
      actualEvenTailCorrectedRealGram
      actualEvenTailCorrectedRealGram_isHermitian hS hD
      actualEvenTailCorrectedRealGram_close hP
  rw [complexOfRealMatrix_actualEvenTailCorrectedRealGram] at hreal
  exact hreal

end

end ArithmeticHodge.Analysis.YoshidaEvenFiniteSchur
