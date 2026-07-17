import ArithmeticHodge.Analysis.CoerciveBilinearWeightedRieszDomination
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedRieszStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailWeightedRieszStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedRieszStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseLowSchur

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-- A positive diagonal reserve in the endpoint-adapted finite-low phase
matrix certifies the canonical corrected Gram whenever it pays for the
weighted energies of the endpoint-adapted Riesz representatives. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_of_weightedRiesz
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1)
    (d gamma : FactorTwoPhaseLowIndex → ℝ)
    (hd : ∀ k, 0 < d k)
    (hreserve : ∀ c : FactorTwoPhaseLowIndex → ℝ,
      ∑ k, d k * c k ^ 2 ≤
        c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c))
    (hrow : ∀ k,
      completedCanonicalPhaseTailBilinear a b hphase
          (canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
            k a b hphase)
          (canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
            k a b hphase) ≤ gamma k)
    (hbudget : ∑ k, gamma k / d k ≤ 1) :
    Matrix.PosSemidef
      (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) := by
  rw [
    completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_sum_endpointAdapted_energy]
  intro c
  have hrow' (k : FactorTwoPhaseLowIndex) :
      completedCanonicalPhaseTailBilinear a b hphase
          (coerciveRieszCorrection
            (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
            (completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
              k a b hphase))
          (coerciveRieszCorrection
            (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
            (completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
              k a b hphase)) ≤ gamma k := by
    simpa only [
      coerciveRieszCorrection_adaptedLowBasisTailRealFunctional] using hrow k
  have henergy :=
    coerciveBilinear_aggregateRiesz_energy_le_of_diagonalReserve
      (K := CanonicalPhaseTailCompletion)
      (factorTwoConcreteLowPhaseMatrix a b)
      (completedCanonicalPhaseTailBilinear a b hphase)
      (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
      (completedCanonicalPhaseTailBilinear_symm a b hphase)
      (fun k ↦ completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
        k a b hphase)
      d gamma hd hreserve hrow' hbudget c
  simpa only [
    coerciveRieszCorrection_adaptedLowBasisTailRealFunctional] using henergy

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailWeightedRieszStructural
