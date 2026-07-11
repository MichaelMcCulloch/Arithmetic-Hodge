/-
  ArithmeticHodge: Toward a Formal Proof of the Arithmetic Hodge Index Theorem

  This project formalizes the chain:
    ZFC → (ℤ, +, ×) → distributive coupling → additive self-duality
    → functional equation → Weil explicit formula → Weil positivity criterion
    → Arithmetic Hodge Index Theorem ⟺ Riemann Hypothesis

  The goal is to reduce the Riemann Hypothesis to the minimum number of
  unproved atomic claims (sorry's), each precisely stated and independently
  attackable.

  DEPENDENCY GRAPH:
  ┌─────────────────────────────────────────────────────────┐
  │  Layer 0: Ring axioms, distributive coupling             │
  │     ↓                                                    │
  │  Layer 1: Poisson summation, theta function,             │
  │           functional equation (axis at 1/2)              │
  │     ↓                                                    │
  │  Layer 2: Weil explicit formula                          │
  │     ↓                                                    │
  │  Layer 3: Weil positivity criterion ⟺ RH                │
  │     ↓                                                    │
  │  Layer 4: Adèle class space, scaling flow,               │
  │           Haar invariance, unitarity                      │
  │     ↓                                                    │
  │  Layer 5: Self-adjoint generator (Stone's thm)           │
  │     ↓                                                    │
  │  Layer 6: Trace formula → Weil positivity [THE GAP]      │
  │     ↓                                                    │
  │  THEOREM: Arithmetic Hodge Index = RH                    │
  └─────────────────────────────────────────────────────────┘
-/

import ArithmeticHodge.Algebra.DistributiveCoupling
import ArithmeticHodge.Analysis.PoissonSummation
import ArithmeticHodge.Analysis.HermitianLowTail
import ArithmeticHodge.Analysis.HilbertTailSchur
import ArithmeticHodge.Analysis.HermitianFormCompletion
import ArithmeticHodge.Analysis.RationalPosDefCertificate
import ArithmeticHodge.Analysis.MatrixAbsEntryComparison
import ArithmeticHodge.Analysis.CoerciveRieszCorrection
import ArithmeticHodge.Analysis.ComplexCoerciveRieszCorrection
import ArithmeticHodge.Analysis.CenteredAddCircleFourier
import ArithmeticHodge.Analysis.ThetaFunction
import ArithmeticHodge.Analysis.ZetaFunctionalEquation
import ArithmeticHodge.Analysis.Contour.ArgumentPrinciple
import ArithmeticHodge.Analysis.Contour.RectangleCauchy
import ArithmeticHodge.Analysis.Contour.RectangleWinding
import ArithmeticHodge.Analysis.Contour.RectangleFiniteResidues
import ArithmeticHodge.Analysis.Contour.RectangleWeightedLogDeriv
import ArithmeticHodge.Analysis.Contour.RectangleMeromorphicGoursat
import ArithmeticHodge.Analysis.Contour.RectangleWeightedArgumentPrinciple
import ArithmeticHodge.Analysis.Contour.XiRectangleArgumentPrinciple
import ArithmeticHodge.Analysis.WeilDefs
import ArithmeticHodge.Analysis.MultiplicativeWeil
import ArithmeticHodge.Analysis.MultiplicativeWeilTranspose
import ArithmeticHodge.Analysis.MultiplicativeWeilVerticalBoundary
import ArithmeticHodge.Analysis.MultiplicativeWeilArchPolarGrowth
import ArithmeticHodge.Analysis.MultiplicativeWeilPrime
import ArithmeticHodge.Analysis.MultiplicativeWeilArchimedean
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadratic
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticMellin
import ArithmeticHodge.Analysis.MultiplicativeWeilSelectedContourExhaustion
import ArithmeticHodge.Analysis.MultiplicativeWeilFunctional
import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import ArithmeticHodge.Analysis.EntireFunction.MinimumModulus
import ArithmeticHodge.Analysis.EntireFunction.Order
import ArithmeticHodge.Analysis.EntireFunction.Hadamard
import ArithmeticHodge.Analysis.ZetaProduct
import ArithmeticHodge.Analysis.ZetaZeroFreeRegionReduction
import ArithmeticHodge.Analysis.ZetaNearOneBound
import ArithmeticHodge.Analysis.ZetaLogDerivPositivity
import ArithmeticHodge.Analysis.ZetaLogDerivRealBound
import ArithmeticHodge.Analysis.ZetaLogDerivRepulsionAlgebra
import ArithmeticHodge.Analysis.ZetaHadamardZeroRepulsion
import ArithmeticHodge.Analysis.ZetaDeLaValleePoussin
import ArithmeticHodge.Analysis.ZetaFunctionalLogDerivative
import ArithmeticHodge.Analysis.MultiplicativeWeilXiBoundary
import ArithmeticHodge.Analysis.MultiplicativeWeilXiHorizontalVanishing
import ArithmeticHodge.Analysis.MultiplicativeWeilFiniteXiContour
import ArithmeticHodge.Analysis.MultiplicativeWeilContourExhaustion
import ArithmeticHodge.Analysis.MultiplicativeWeilContourLimitAlgebra
import ArithmeticHodge.Analysis.MultiplicativeWeilArchPolarLimit
import ArithmeticHodge.Analysis.MultiplicativeWeilExplicitFormula
import ArithmeticHodge.Analysis.MultiplicativeWeilZeros
import ArithmeticHodge.Analysis.MultiplicativeWeilCriterion
import ArithmeticHodge.Analysis.MultiplicativeWeilLiAlgebra
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticSupport
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticCriticalLine
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticEndpoint
import ArithmeticHodge.Analysis.MultiplicativeWeilLocalCriticalForm
import ArithmeticHodge.Analysis.YoshidaClippedDomain
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticPolarBound
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticReality
import ArithmeticHodge.Analysis.MultiplicativeWeilSmallSupportPositivity
import ArithmeticHodge.Analysis.MultiplicativeWeilLiKernel
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoff
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoffSpectral
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoffFormula
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCutoffTsum
import ArithmeticHodge.Analysis.MultiplicativeWeilLiSmoothConvolution
import ArithmeticHodge.Analysis.MultiplicativeWeilLiSmoothSpectralTransfer
import ArithmeticHodge.Analysis.MultiplicativeWeilLiOffCritical
import ArithmeticHodge.Analysis.MultiplicativeWeilLiPhaseRecurrence
import ArithmeticHodge.Analysis.MultiplicativeWeilLiSeries
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroPowerSummability
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroLogSummability
import ArithmeticHodge.Analysis.MultiplicativeWeilLiDominantSeries
import ArithmeticHodge.Analysis.MultiplicativeWeilLiCriterionClosure
import ArithmeticHodge.Analysis.MultiplicativeWeilApproximateIdentity
import ArithmeticHodge.Analysis.MultiplicativeWeilMellinApproximateIdentity
import ArithmeticHodge.Analysis.MultiplicativeWeilMellinBumpSequence
import ArithmeticHodge.Analysis.MultiplicativeWeilMellinFourier
import ArithmeticHodge.Analysis.MultiplicativeWeilLogSupport
import ArithmeticHodge.Analysis.MultiplicativeWeilDilation
import ArithmeticHodge.Analysis.CompactSupportLogUncertainty
import ArithmeticHodge.Analysis.MultiplicativeWeilArchimedeanKernel
import ArithmeticHodge.Analysis.MultiplicativeWeilArchimedeanSeries
import ArithmeticHodge.Analysis.MultiplicativeWeilCriticalGammaPair
import ArithmeticHodge.Analysis.MultiplicativeWeilDigamma
import ArithmeticHodge.Analysis.TrapezoidalErrorBounds
import ArithmeticHodge.Analysis.DigammaTrapezoid
import ArithmeticHodge.Analysis.DigammaTrapezoidBounds
import ArithmeticHodge.Analysis.DigammaNumericBounds
import ArithmeticHodge.Analysis.MultiplicativeWeilDigammaLower
import ArithmeticHodge.Analysis.MultiplicativeWeilDigammaIntegral
import ArithmeticHodge.Analysis.MultiplicativeWeilDigammaSummation
import ArithmeticHodge.Analysis.MultiplicativeWeilGammaIntegral
import ArithmeticHodge.Analysis.MultiplicativeWeilHorizontalEdge
import ArithmeticHodge.Analysis.MultiplicativeWeilGammaArchimedean
import ArithmeticHodge.Analysis.MultiplicativeWeilHarmonicConstant
import ArithmeticHodge.Analysis.MultiplicativeWeilWeightedMellin
import ArithmeticHodge.Analysis.MultiplicativeWeilDirichletInterchange
import ArithmeticHodge.Analysis.MultiplicativeWeilZetaPrimeIntegral
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroFiberSum
import ArithmeticHodge.Analysis.MultiplicativeWeilZeroSummability
import ArithmeticHodge.Analysis.MultiplicativeWeilDistinctZeroSum
import ArithmeticHodge.Analysis.EntireFunction.CompletedZetaZeroExponent
import ArithmeticHodge.Analysis.ZetaZeroCount
import ArithmeticHodge.Analysis.XiZeroMultiplicity
import ArithmeticHodge.Analysis.XiRectangleContourData
import ArithmeticHodge.Analysis.XiZeroFreeHeight
import ArithmeticHodge.Analysis.XiLogDerivGrowth
import ArithmeticHodge.Analysis.XiQuantitativeZeroFreeHeight
import ArithmeticHodge.Analysis.XiContourSequence
import ArithmeticHodge.Analysis.XiZetaMultiplicityBridge
import ArithmeticHodge.Analysis.XiZetaZeroEquiv
import ArithmeticHodge.Analysis.WeilExplicit
import ArithmeticHodge.Analysis.FourierTransform
import ArithmeticHodge.Analysis.WeilPositivity
import ArithmeticHodge.Adelic.ClassSpace
import ArithmeticHodge.Adelic.SelbergUnfolding
import ArithmeticHodge.Adelic.TateLocalComputation
import ArithmeticHodge.Spectral.UnboundedOperator
import ArithmeticHodge.Spectral.SelfAdjointness
import ArithmeticHodge.Spectral.SpectralPositivity
import ArithmeticHodge.Spectral.ResolventComputation
import ArithmeticHodge.Spectral.TraceFormula
import ArithmeticHodge.Adelic.OrbitalIntegrals
import ArithmeticHodge.Arithmetic.HodgeIndex
import ArithmeticHodge.Strategy.DetailedBalance
