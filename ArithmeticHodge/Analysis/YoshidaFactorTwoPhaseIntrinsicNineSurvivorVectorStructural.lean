import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineDirectMatrixStructural

set_option autoImplicit false

open Matrix

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineSurvivorVectorStructural

noncomputable section

open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOcticPotential
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural

/-!
# The exact cutoff-nine survivor vector

The coordinate order is the direct-matrix order

`(c0,c2,c4,c1,c3,c5,c6,c8,c7)`.

Each row is the exact low--tail mixed evaluation on the corresponding
centered Legendre basis pair.  On the last three rows, the already-certified
`P6/P7/P8` forward family is subtracted before the row is retained.
-/

/-- Exact basis-evaluation vector of the cutoff-nine survivor. -/
def factorTwoIntrinsicNineSurvivorVector
    (eR oR : ℝ → ℝ) (a b : ℝ) : Fin 9 → ℝ :=
  ![
    factorTwoEndpointLowTailMixed centeredEvenP0 eR 0 oR a b,
    factorTwoEndpointLowTailMixed centeredEvenP2 eR 0 oR a b,
    factorTwoEndpointLowTailMixed factorTwoCenteredP4 eR 0 oR a b,
    factorTwoEndpointLowTailMixed 0 eR centeredP1 oR a b,
    factorTwoEndpointLowTailMixed 0 eR centeredP3 oR a b,
    factorTwoEndpointLowTailMixed 0 eR factorTwoCenteredP5 oR a b,
    factorTwoEndpointLowTailMixed factorTwoCenteredP6 eR 0 oR a b -
      factorTwoP678ResidualCombinedForwardMixed eR oR 1 0 0 a b,
    factorTwoEndpointLowTailMixed factorTwoCenteredP8 eR 0 oR a b -
      factorTwoP678ResidualCombinedForwardMixed eR oR 0 0 1 a b,
    factorTwoEndpointLowTailMixed 0 eR factorTwoCenteredP7 oR a b -
      factorTwoP678ResidualCombinedForwardMixed eR oR 0 1 0 a b
  ]

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineSurvivorVectorStructural
