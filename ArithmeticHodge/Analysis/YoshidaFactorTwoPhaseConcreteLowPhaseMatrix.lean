import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowMatrix
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanOddMatrix

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowPhaseMatrix

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
open YoshidaFactorTwoPhaseConcreteCleanOddMatrix
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseLowSchur

/-!
# Fully concrete finite low phase matrix

This module assembles the two clean Gram blocks, the two symmetric
factor-two perturbation blocks, and the alternating even--odd block into the
exact `200 + 10` phase matrix.
-/

/-- The fully concrete endpoint-adapted `200 + 10` low phase matrix. -/
def factorTwoConcreteLowPhaseMatrix (a b : ℝ) :
    Matrix FactorTwoPhaseLowIndex FactorTwoPhaseLowIndex ℝ :=
  factorTwoFiniteLowPhaseMatrix
    factorTwoConcreteAdaptedEvenCleanMatrix
    factorTwoConcreteEvenPerturbationMatrix
    factorTwoConcreteOddCleanMatrix
    factorTwoConcreteOddPerturbationMatrix
    factorTwoConcreteAlternatingMatrix a b

/-- The five concrete blocks represent the endpoint channel phase exactly
on the endpoint-adapted even and canonical odd low syntheses. -/
theorem factorTwoConcreteLowPhaseMatrix_represents
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) :
    factorTwoEndpointChannelPhase
        (factorTwoAdaptedEvenLowSynthesis e)
        (factorTwoOddLowSynthesis o) a b =
      let c := factorTwoPhaseLowCoefficients e o
      c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) := by
  simpa only [factorTwoConcreteLowPhaseMatrix] using
    factorTwoFiniteLowPhaseMatrix_represents
      factorTwoConcreteAdaptedEvenCleanMatrix
      factorTwoConcreteEvenPerturbationMatrix
      factorTwoConcreteOddCleanMatrix
      factorTwoConcreteOddPerturbationMatrix
      factorTwoConcreteAlternatingMatrix
      e o
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b
      (factorTwoConcreteAdaptedEvenCleanMatrix_represents e)
      (factorTwoConcreteOddCleanMatrix_represents o)
      (factorTwoConcreteEvenPerturbationMatrix_represents e)
      (factorTwoConcreteOddPerturbationMatrix_represents o)
      (factorTwoConcreteAlternatingMatrix_represents e o)

/-- Positive semidefiniteness of the concrete matrix at one phase implies
nonnegativity of the corresponding synthesized low phase. -/
theorem factorTwoConcreteLowPhase_nonneg_of_posSemidef
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ)
    (hPSD : (factorTwoConcreteLowPhaseMatrix a b).PosSemidef) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b := by
  rw [factorTwoConcreteLowPhaseMatrix_represents]
  exact hPSD.dotProduct_mulVec_nonneg (factorTwoPhaseLowCoefficients e o)

/-- A disk-uniform positive-semidefinite certificate for the concrete matrix
closes every endpoint-adapted finite-low phase on `a² + b² ≤ 1`. -/
theorem factorTwoConcreteLowPhase_nonneg_of_disk_posSemidef
    (hPSD : ∀ a b : ℝ, a ^ 2 + b ^ 2 ≤ 1 →
      (factorTwoConcreteLowPhaseMatrix a b).PosSemidef)
    (e : YoshidaEvenIndex → ℝ) (o : YoshidaOddIndex → ℝ)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase
      (factorTwoAdaptedEvenLowSynthesis e)
      (factorTwoOddLowSynthesis o) a b :=
  factorTwoConcreteLowPhase_nonneg_of_posSemidef e o a b
    (hPSD a b hab)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
