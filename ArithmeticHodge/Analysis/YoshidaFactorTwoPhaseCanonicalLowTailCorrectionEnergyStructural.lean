import ArithmeticHodge.Analysis.CoerciveBilinearSchurCharacterization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaEndpointScaledCorrelation
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointParityPencil
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseLowSchur
open YoshidaWeightedTailBounds

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

private theorem factorTwoCanonicalEvenCleanMatrix_isHermitian :
    factorTwoCanonicalEvenCleanMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := yoshidaClippedLocalCriticalForm_conj_apply yoshidaA_pos
    (yoshidaClippedEvenLowMode yoshidaA i)
    (yoshidaClippedEvenLowMode yoshidaA j)
  simpa only [factorTwoCanonicalEvenCleanMatrix, star_trivial] using
    congrArg (fun z : ℂ ↦ z.re / yoshidaA) h

private theorem factorTwoCanonicalEvenPerturbationMatrix_isHermitian :
    factorTwoCanonicalEvenPerturbationMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [factorTwoCanonicalEvenPerturbationMatrix,
    factorTwoCanonicalEvenPerturbationEntry, star_trivial]
  rw [factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
      _ _ (continuous_factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEvenLowIndex j))
        (continuous_factorTwoCenteredCanonicalEvenProfile
          (factorTwoCanonicalEvenLowIndex i)),
    factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
      _ _ (continuous_factorTwoCenteredCanonicalEvenProfile
        (factorTwoCanonicalEvenLowIndex i))
        (continuous_factorTwoCenteredCanonicalEvenProfile
          (factorTwoCanonicalEvenLowIndex j)),
    factorTwoCenteredSymmetricPerturbationPolarization_comm]

private theorem factorTwoConcreteOddPerturbationMatrix_isHermitian :
    factorTwoConcreteOddPerturbationMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [factorTwoConcreteOddPerturbationMatrix, star_trivial]
  rw [factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
      _ _ (continuous_factorTwoCenteredOddLowProfile j)
        (continuous_factorTwoCenteredOddLowProfile i),
    factorTwoCenteredSymmetricPerturbationBilinear_eq_polarization
      _ _ (continuous_factorTwoCenteredOddLowProfile i)
        (continuous_factorTwoCenteredOddLowProfile j),
    factorTwoCenteredSymmetricPerturbationPolarization_comm]

private theorem add_smul_isHermitian_real
    {n : Type*} {Q P : Matrix n n ℝ}
    (hQ : Q.IsHermitian) (hP : P.IsHermitian) (a : ℝ) :
    (Q + a • P).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hq := hQ.apply i j
  have hp := hP.apply i j
  simpa only [add_apply, smul_apply, smul_eq_mul, star_trivial] using
    congrArg₂ (fun x y : ℝ ↦ x + a * y) hq hp

/-- The canonical one-copy finite-low phase matrix is Hermitian before any
positivity certificate is chosen. -/
theorem canonicalPhaseLowMatrix_isHermitian (a b : ℝ) :
    (canonicalPhaseLowMatrix a b).IsHermitian := by
  unfold canonicalPhaseLowMatrix factorTwoFiniteLowPhaseMatrix
  apply factorTwoPhaseBlockMatrix_isHermitian
  · exact add_smul_isHermitian_real
      factorTwoCanonicalEvenCleanMatrix_isHermitian
      factorTwoCanonicalEvenPerturbationMatrix_isHermitian a
  · exact add_smul_isHermitian_real
      factorTwoConcreteOddCleanMatrix_isHermitian
      factorTwoConcreteOddPerturbationMatrix_isHermitian a

/-- Aggregate real-coordinate Riesz correction selected by one finite-low
coefficient vector. -/
def canonicalPhaseLowTailRealRieszCombination
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) : CanonicalPhaseTailCompletion :=
  ∑ k, c k • canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase

private theorem completedCanonicalPhaseLowTailRealCorrectedGram_eq_coercive
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    completedCanonicalPhaseLowTailRealCorrectedGram a b hphase =
      coerciveBilinearCorrectedGram
        (canonicalPhaseLowMatrix a b)
        (completedCanonicalPhaseTailBilinear a b hphase)
        (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
        (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
          k a b hphase) := by
  ext k l
  rfl

/-- Exact structural characterization of the remaining reduced certificate:
the `210 × 210` corrected Gram is PSD iff the finite-low phase energy
dominates the energy of the single aggregate tail representer. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_energy
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) ↔
      ∀ c : FactorTwoPhaseLowIndex → ℝ,
        completedCanonicalPhaseTailBilinear a b hphase
            (canonicalPhaseLowTailRealRieszCombination c a b hphase)
            (canonicalPhaseLowTailRealRieszCombination c a b hphase) ≤
          c ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ c) := by
  rw [completedCanonicalPhaseLowTailRealCorrectedGram_eq_coercive]
  simpa only [canonicalPhaseLowTailRealRieszCombination,
    canonicalPhaseLowBasisTailRealRieszCorrection] using
    (coerciveBilinearCorrectedGram_posSemidef_iff_energy
      (K := CanonicalPhaseTailCompletion)
      (canonicalPhaseLowMatrix a b)
      (completedCanonicalPhaseTailBilinear a b hphase)
      (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
      (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
        k a b hphase)
      (canonicalPhaseLowMatrix_isHermitian a b)
      (completedCanonicalPhaseTailBilinear_symm a b hphase))

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural
