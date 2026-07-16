import ArithmeticHodge.Analysis.CoerciveBilinearFiniteSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseLowSchur

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-- The canonical `200 + 10` finite-low matrix at a fixed disk phase. -/
def canonicalPhaseLowMatrix (a b : ℝ) :
    Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ :=
  factorTwoFiniteLowPhaseMatrix
    factorTwoCanonicalEvenCleanMatrix
    factorTwoCanonicalEvenPerturbationMatrix
    factorTwoConcreteOddCleanMatrix
    factorTwoConcreteOddPerturbationMatrix
    factorTwoCanonicalAlternatingMatrix a b

/-- Real and imaginary copies of the canonical finite-low coordinate space. -/
abbrev CanonicalPhaseLowRealImagIndex :=
  FactorTwoPhaseLowIndex ⊕ FactorTwoPhaseLowIndex

/-- Pack the real and imaginary low-coordinate vectors. -/
def canonicalPhaseLowRealImagCoefficients
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ) :
    CanonicalPhaseLowRealImagIndex → ℝ :=
  Sum.elim cReal cImag

/-- Duplicate a real low matrix on the real and imaginary coordinate blocks,
with no artificial cross term. -/
def duplicatePhaseLowMatrix
    (A : Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ) :
    Matrix CanonicalPhaseLowRealImagIndex CanonicalPhaseLowRealImagIndex ℝ
  | Sum.inl i, Sum.inl j => A i j
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr i, Sum.inr j => A i j

/-- The two-copy canonical low matrix for a complex low profile. -/
def canonicalPhaseLowRealImagMatrix (a b : ℝ) :
    Matrix CanonicalPhaseLowRealImagIndex CanonicalPhaseLowRealImagIndex ℝ :=
  duplicatePhaseLowMatrix (canonicalPhaseLowMatrix a b)

/-- The completed mixed functional selected by a real or imaginary low
coordinate. -/
def completedCanonicalPhaseLowRealImagFunctional
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhaseLowRealImagIndex →
      StrongDual ℝ CanonicalPhaseTailCompletion
  | Sum.inl k =>
      completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase
  | Sum.inr k =>
      completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase

/-- The corresponding family of coercive Riesz corrections in the shared
completed tail space. -/
def canonicalPhaseLowRealImagRieszCorrection
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    CanonicalPhaseLowRealImagIndex → CanonicalPhaseTailCompletion
  | Sum.inl k => canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase
  | Sum.inr k => canonicalPhaseLowBasisTailImagRieszCorrection k a b hphase

@[simp] theorem canonicalPhaseLowRealImagRieszCorrection_eq_coercive
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (p : CanonicalPhaseLowRealImagIndex) :
    canonicalPhaseLowRealImagRieszCorrection a b hphase p =
      coerciveRieszCorrection
        (V := CanonicalPhaseTailCompletion)
        (B := completedCanonicalPhaseTailBilinear a b hphase)
        (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
        (completedCanonicalPhaseLowRealImagFunctional a b hphase p) := by
  cases p <;> rfl

/-- The honest Schur complement on all `420` real low coordinates.  Its
off-diagonal real--imaginary blocks are retained until an orthogonality
symmetry proves that they vanish. -/
def completedCanonicalPhaseLowTailCorrectedGram
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix CanonicalPhaseLowRealImagIndex CanonicalPhaseLowRealImagIndex ℝ :=
  coerciveBilinearCorrectedGram
    (K := CanonicalPhaseTailCompletion)
    (canonicalPhaseLowRealImagMatrix a b)
    (completedCanonicalPhaseTailBilinear a b hphase)
    (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
    (completedCanonicalPhaseLowRealImagFunctional a b hphase)

/-- Exact completion of the square for the simultaneous real and imaginary
canonical low blocks coupled to their one shared completed tail. -/
theorem completedCanonicalPhaseLowTail_complete_square
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (d : CanonicalPhaseLowRealImagIndex → ℝ)
    (z : CanonicalPhaseTailCompletion) :
    d ⬝ᵥ (canonicalPhaseLowRealImagMatrix a b *ᵥ d) +
        2 * ∑ p, d p *
          completedCanonicalPhaseLowRealImagFunctional a b hphase p z +
        completedCanonicalPhaseTailBilinear a b hphase z z =
      d ⬝ᵥ (completedCanonicalPhaseLowTailCorrectedGram a b hphase *ᵥ d) +
        completedCanonicalPhaseTailBilinear a b hphase
          (z + ∑ p, d p •
            canonicalPhaseLowRealImagRieszCorrection a b hphase p)
          (z + ∑ p, d p •
            canonicalPhaseLowRealImagRieszCorrection a b hphase p) := by
  simpa only [completedCanonicalPhaseLowTailCorrectedGram,
    canonicalPhaseLowRealImagRieszCorrection_eq_coercive] using
    (coerciveBilinear_complete_square
      (K := CanonicalPhaseTailCompletion)
      (canonicalPhaseLowRealImagMatrix a b)
      (completedCanonicalPhaseTailBilinear a b hphase)
      (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
      (completedCanonicalPhaseTailBilinear_symm a b hphase)
      (completedCanonicalPhaseLowRealImagFunctional a b hphase) d z)

/-- Positive semidefiniteness of the honest corrected Gram is exactly the
remaining finite Schur certificate for the assembled low--tail quadratic. -/
theorem completedCanonicalPhaseLowTail_nonneg_of_correctedGram_posSemidef
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (hG : Matrix.PosSemidef
      (completedCanonicalPhaseLowTailCorrectedGram a b hphase))
    (d : CanonicalPhaseLowRealImagIndex → ℝ)
    (z : CanonicalPhaseTailCompletion) :
    0 ≤ d ⬝ᵥ (canonicalPhaseLowRealImagMatrix a b *ᵥ d) +
      2 * ∑ p, d p *
        completedCanonicalPhaseLowRealImagFunctional a b hphase p z +
      completedCanonicalPhaseTailBilinear a b hphase z z := by
  exact coerciveBilinear_full_nonneg_of_correctedGram_posSemidef
    (K := CanonicalPhaseTailCompletion)
    (canonicalPhaseLowRealImagMatrix a b)
    (completedCanonicalPhaseTailBilinear a b hphase)
    (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
    (completedCanonicalPhaseTailBilinear_symm a b hphase)
    (completedCanonicalPhaseLowRealImagFunctional a b hphase) hG d z

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
