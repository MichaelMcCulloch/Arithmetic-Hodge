import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseLowSchur

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-- The coercive Riesz representative of the real-coordinate mixed interaction
between a canonical low mode and the completed canonical tail. -/
def canonicalPhaseLowBasisTailRealRieszCorrection
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) : CanonicalPhaseTailCompletion :=
  coerciveRieszCorrection
    (V := CanonicalPhaseTailCompletion)
    (B := completedCanonicalPhaseTailBilinear a b hphase)
    (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
    (completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase)

/-- The coercive Riesz representative of the imaginary-coordinate mixed
interaction between a canonical low mode and the completed canonical tail. -/
def canonicalPhaseLowBasisTailImagRieszCorrection
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) : CanonicalPhaseTailCompletion :=
  coerciveRieszCorrection
    (V := CanonicalPhaseTailCompletion)
    (B := completedCanonicalPhaseTailBilinear a b hphase)
    (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
    (completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase)

/-- The real-coordinate correction represents the completed mixed
functional exactly against the canonical tail form. -/
theorem completedCanonicalPhaseTailBilinear_realRieszCorrection_apply
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) (z : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseLowBasisTailRealRieszCorrection k a b hphase) z =
      completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase z := by
  exact coerciveRieszCorrection_apply
    (V := CanonicalPhaseTailCompletion)
    (B := completedCanonicalPhaseTailBilinear a b hphase)
    (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
    (completedCanonicalPhaseLowBasisTailRealFunctional k a b hphase) z

/-- The imaginary-coordinate correction represents the completed mixed
functional exactly against the canonical tail form. -/
theorem completedCanonicalPhaseTailBilinear_imagRieszCorrection_apply
    (k : FactorTwoPhaseLowIndex) (a b : ℝ)
    (hphase : a ^ 2 + b ^ 2 ≤ 1) (z : CanonicalPhaseTailCompletion) :
    completedCanonicalPhaseTailBilinear a b hphase
        (canonicalPhaseLowBasisTailImagRieszCorrection k a b hphase) z =
      completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase z := by
  exact coerciveRieszCorrection_apply
    (V := CanonicalPhaseTailCompletion)
    (B := completedCanonicalPhaseTailBilinear a b hphase)
    (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
    (completedCanonicalPhaseLowBasisTailImagFunctional k a b hphase) z

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailRieszStructural
