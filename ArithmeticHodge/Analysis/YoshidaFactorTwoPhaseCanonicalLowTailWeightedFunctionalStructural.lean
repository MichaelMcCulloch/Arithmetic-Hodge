import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailWeightedRieszStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailWeightedFunctionalStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaCoercivityNumerics
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedRieszStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailWeightedRieszStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseCanonicalTailDiagonalStructural
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseLowSchur
open YoshidaWeightedTailBounds

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-- The explicit coercivity constant converts the endpoint-adapted functional
norm into a certified energy bound for its Riesz representative. -/
theorem completedCanonicalPhaseAdaptedLowBasisTailRealRiesz_energy_le_norm
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
          k a b hphase)
        (canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
          k a b hphase) ≤
      ‖completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
          k a b hphase‖ ^ 2 / (1 / (200 * yoshidaA)) := by
  rw [← coerciveRieszCorrection_adaptedLowBasisTailRealFunctional]
  apply coerciveRieszCorrection_energy_le
  · exact one_div_pos.mpr (mul_pos (by norm_num) yoshidaA_pos)
  · exact completionBilinearExtension_diagonal_lower_bound
      (canonicalPhaseTailCoreContinuousBilinear a b hphase)
      (1 / (200 * yoshidaA))
      (fun x ↦ by
        simpa only [canonicalPhaseTailCoreContinuousBilinear_apply,
          canonicalPhaseTailCoreBilinearValue_self, pow_two, mul_assoc] using
          (canonicalPhaseTailCoreDiagonal_coercive x a b hphase))

/-- A positive diagonal reserve and one weighted operator-norm budget certify
the full endpoint-adapted low-tail Schur complement. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_of_functionalNormBudget
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (d : FactorTwoPhaseLowIndex → ℝ)
    (hd : ∀ k, 0 < d k)
    (hreserve : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      ∑ k, d k * c k ^ 2 ≤
        c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c))
    (hbudget :
      ∑ k,
          (‖completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
              k a b hphase‖ ^ 2 / (1 / (200 * yoshidaA))) / d k ≤ 1) :
    Matrix.PosSemidef
      (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) := by
  apply completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_of_weightedRiesz
    a b hphase d
    (fun k ↦
      ‖completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
          k a b hphase‖ ^ 2 / (1 / (200 * yoshidaA)))
    hd hreserve
  · exact fun k ↦
      completedCanonicalPhaseAdaptedLowBasisTailRealRiesz_energy_le_norm
        k a b hphase
  · exact hbudget

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailWeightedFunctionalStructural
