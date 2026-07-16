import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointShearStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedRieszStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailEndpointShearStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
open YoshidaFactorTwoPhaseEndpointAdaptedLow
open YoshidaFactorTwoPhaseLowSchur

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-- Endpoint trace coefficient of one packed canonical low basis vector. -/
def canonicalPhaseMode200BasisCoefficient :
    FactorTwoPhaseLowIndex → ℝ
  | Sum.inl i => endpointEvenLowTraceRatio i
  | Sum.inr _ => 0

/-- Frequency-`200` tail shift attached to one packed low basis vector. -/
def canonicalPhaseMode200BasisShift
    (k : FactorTwoPhaseLowIndex) : CanonicalPhaseTailCompletion :=
  canonicalPhaseMode200BasisCoefficient k •
    (canonicalPhaseMode200Core : CanonicalPhaseTailCompletion)

/-- Summing the basis shifts gives exactly the aggregate endpoint shift used
by the physical shear. -/
theorem sum_canonicalPhaseMode200BasisShift
    (c : FactorTwoPhaseLowIndex → ℝ) :
    ∑ k, c k • canonicalPhaseMode200BasisShift k =
      canonicalPhaseLowMode200Shift c := by
  classical
  unfold canonicalPhaseMode200BasisShift
    canonicalPhaseMode200BasisCoefficient
    canonicalPhaseLowMode200Shift canonicalPhaseLowMode200ShiftCore
  rw [Fintype.sum_sum_type]
  simp only [smul_smul]
  rw [← Finset.sum_smul, ← Finset.sum_smul]
  unfold YoshidaFactorTwoPhaseEndpointAdaptedDecomposition.evenLowEndpointCorrectionCoefficient
    YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural.canonicalPhaseLowEvenCoefficients
  simp only [UniformSpace.Completion.coe_smul, mul_zero, Finset.sum_const_zero]
  rw [show (0 : ℝ) •
      (canonicalPhaseMode200Core : CanonicalPhaseTailCompletion) = 0 by
        exact zero_smul (M₀ := ℝ)
          (canonicalPhaseMode200Core : CanonicalPhaseTailCompletion)]
  exact add_zero _

/-- The completed mixed functional of one endpoint-adapted low basis vector,
defined by the exact mode-`200` shear of the canonical functional. -/
def completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    StrongDual ℝ CanonicalPhaseTailCompletion :=
  coerciveBilinearShearedFunctional
    (completedCanonicalPhaseTailBilinear a b hphase)
    (fun q ↦ completedCanonicalPhaseLowBasisTailRealFunctional
      q a b hphase)
    canonicalPhaseMode200BasisShift k

/-- Explicit endpoint-adapted Riesz correction for one low basis vector. -/
def canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) : CanonicalPhaseTailCompletion :=
  canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase -
    canonicalPhaseMode200BasisShift k

/-- The explicit shifted vector is exactly the coercive Riesz representative
of the endpoint-adapted mixed functional. -/
theorem coerciveRieszCorrection_adaptedLowBasisTailRealFunctional
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    coerciveRieszCorrection
        (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
        (completedCanonicalPhaseAdaptedLowBasisTailRealFunctional
          k a b hphase) =
      canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
        k a b hphase := by
  simpa only [completedCanonicalPhaseAdaptedLowBasisTailRealFunctional,
    canonicalPhaseAdaptedLowBasisTailRealRieszCorrection,
    canonicalPhaseLowBasisTailRealRieszCorrection] using
    (coerciveRieszCorrection_shearedFunctional
      (completedCanonicalPhaseTailBilinear a b hphase)
      (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
      (fun q ↦ completedCanonicalPhaseLowBasisTailRealFunctional
        q a b hphase)
      canonicalPhaseMode200BasisShift k)

/-- The endpoint-cancelled aggregate representer is the literal linear
combination of the endpoint-adapted basis Riesz corrections. -/
theorem sum_canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
    (c : FactorTwoPhaseLowIndex → ℝ) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    ∑ k, c k • canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
        k a b hphase =
      canonicalPhaseAdaptedLowTailRealRieszCombination c a b hphase := by
  unfold canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
    canonicalPhaseAdaptedLowTailRealRieszCombination
    canonicalPhaseLowTailRealRieszCombination
  calc
    ∑ k, c k • (canonicalPhaseLowBasisTailRealRieszCorrection
        k a b hphase - canonicalPhaseMode200BasisShift k) =
        ∑ k, (c k • canonicalPhaseLowBasisTailRealRieszCorrection
          k a b hphase - c k • canonicalPhaseMode200BasisShift k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact smul_sub (c k)
        (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase)
        (canonicalPhaseMode200BasisShift k)
    _ = (∑ k, c k • canonicalPhaseLowBasisTailRealRieszCorrection
          k a b hphase) - canonicalPhaseLowMode200Shift c := by
      rw [Finset.sum_sub_distrib, sum_canonicalPhaseMode200BasisShift]

/-- Per-basis form of the exact endpoint-adapted energy target.  This is the
shape needed by structural row-energy or weighted Loewner estimates. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_sum_endpointAdapted_energy
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) ↔
      ∀ c : FactorTwoPhaseLowIndex → ℝ,
        completedCanonicalPhaseTailBilinear a b hphase
            (∑ k, c k •
              canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
                k a b hphase)
            (∑ k, c k •
              canonicalPhaseAdaptedLowBasisTailRealRieszCorrection
                k a b hphase) ≤
          c ⬝ᵥ (factorTwoConcreteLowPhaseMatrix a b *ᵥ c) := by
  simpa only [sum_canonicalPhaseAdaptedLowBasisTailRealRieszCorrection] using
    (completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_endpointAdapted_energy
      a b hphase)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailEndpointAdaptedRieszStructural
