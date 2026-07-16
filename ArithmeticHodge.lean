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
import ArithmeticHodge.Analysis.RationalInterval
import ArithmeticHodge.Analysis.RationalIntervalSchur
import ArithmeticHodge.Analysis.RobustCongruenceCertificate
import ArithmeticHodge.Analysis.MatrixAbsEntryComparison
import ArithmeticHodge.Analysis.YoshidaOddComparisonCertificate
import ArithmeticHodge.Analysis.YoshidaOddGramPrefix
import ArithmeticHodge.Analysis.YoshidaClippedMomentBridge
import ArithmeticHodge.Analysis.YoshidaClippedMomentBridgeFull
import ArithmeticHodge.Analysis.YoshidaMomentIntegrability
import ArithmeticHodge.Analysis.YoshidaCauchyTailBounds
import ArithmeticHodge.Analysis.YoshidaMomentSeries
import ArithmeticHodge.Analysis.YoshidaDiagonalMomentSeries
import ArithmeticHodge.Analysis.YoshidaDiagonalSeriesTail
import ArithmeticHodge.Analysis.YoshidaSineSeriesTail
import ArithmeticHodge.Analysis.YoshidaSineMomentEnclosures
import ArithmeticHodge.Analysis.YoshidaDigammaDistribution
import ArithmeticHodge.Analysis.YoshidaCauchyPairing
import ArithmeticHodge.Analysis.YoshidaOddModeRegularity
import ArithmeticHodge.Analysis.YoshidaOddFourierDecay
import ArithmeticHodge.Analysis.YoshidaOddSpectralBridge
import ArithmeticHodge.Analysis.YoshidaOddCorrelationFold
import ArithmeticHodge.Analysis.YoshidaOddPolarCorrelation
import ArithmeticHodge.Analysis.YoshidaRenormalizedGeometricKernel
import ArithmeticHodge.Analysis.YoshidaShiftedGeometricSeries
import ArithmeticHodge.Analysis.YoshidaOddCorrelationIntegrability
import ArithmeticHodge.Analysis.YoshidaOddRealSpaceAssembly
import ArithmeticHodge.Analysis.YoshidaDiagonalAcceleratedSeries
import ArithmeticHodge.Analysis.YoshidaDiagonalMomentEnclosures
import ArithmeticHodge.Analysis.YoshidaDiagonalHigherAcceleration
import ArithmeticHodge.Analysis.YoshidaOddIntervalCertificate
import ArithmeticHodge.Analysis.YoshidaOddMomentTargets
import ArithmeticHodge.Analysis.YoshidaOddComparisonReserve
import ArithmeticHodge.Analysis.YoshidaOddGramPosDef
import ArithmeticHodge.Analysis.CoerciveRieszCorrection
import ArithmeticHodge.Analysis.ComplexCoerciveRieszCorrection
import ArithmeticHodge.Analysis.BilinearFormCompletion
import ArithmeticHodge.Analysis.CenteredAddCircleFourier
import ArithmeticHodge.Analysis.YoshidaClippedCircleBridge
import ArithmeticHodge.Analysis.YoshidaClippedCircleFaithful
import ArithmeticHodge.Analysis.YoshidaClippedPeriodicCore
import ArithmeticHodge.Analysis.YoshidaRestrictedCoreBridge
import ArithmeticHodge.Analysis.YoshidaClippedParityOrthogonality
import ArithmeticHodge.Analysis.YoshidaEvenPairingBridge
import ArithmeticHodge.Analysis.YoshidaEvenTailReduction
import ArithmeticHodge.Analysis.YoshidaEvenCouplingReduction
import ArithmeticHodge.Analysis.YoshidaEvenDigammaImagRemainder
import ArithmeticHodge.Analysis.YoshidaEvenPairingEquation
import ArithmeticHodge.Analysis.YoshidaEvenHomogeneousCoercivity
import ArithmeticHodge.Analysis.YoshidaEvenTailLowFunctional
import ArithmeticHodge.Analysis.YoshidaOddLowHighDecay
import ArithmeticHodge.Analysis.YoshidaOddHighSineBounds
import ArithmeticHodge.Analysis.YoshidaOddCouplingClosed
import ArithmeticHodge.Analysis.YoshidaInfiniteCriticalSample
import ArithmeticHodge.Analysis.YoshidaOddTailPaired
import ArithmeticHodge.Analysis.YoshidaOddDigammaLoss
import ArithmeticHodge.Analysis.YoshidaOddDigammaRationalCertificate
import ArithmeticHodge.Analysis.YoshidaOddDigammaIntegralCertificate
import ArithmeticHodge.Analysis.YoshidaOddDigammaSplit
import ArithmeticHodge.Analysis.YoshidaOddSpectralMassBridge
import ArithmeticHodge.Analysis.YoshidaOddPolarBound
import ArithmeticHodge.Analysis.YoshidaOddCoercivityAssembly
import ArithmeticHodge.Analysis.YoshidaOddHomogeneousCoercivity
import ArithmeticHodge.Analysis.YoshidaOddTailLowFunctional
import ArithmeticHodge.Analysis.YoshidaOddInfiniteSchur
import ArithmeticHodge.Analysis.YoshidaParityRecombination
import ArithmeticHodge.Analysis.YoshidaEvenIntervalCertificate
import ArithmeticHodge.Analysis.YoshidaClippedEvenMomentBridge
import ArithmeticHodge.Analysis.YoshidaEvenDistributionReduction
import ArithmeticHodge.Analysis.YoshidaEvenCriticalCrossBridge
import ArithmeticHodge.Analysis.YoshidaEvenMomentTargets
import ArithmeticHodge.Analysis.YoshidaEvenZeroMomentEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenDiagonalOneEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenDiagonalTwoEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenDiagonalThreeEnclosure
import ArithmeticHodge.Analysis.YoshidaSineAcceleratedTail
import ArithmeticHodge.Analysis.YoshidaSineAcceleratedEnclosures
import ArithmeticHodge.Analysis.YoshidaSineCheckpointedHead
import ArithmeticHodge.Analysis.YoshidaEvenSineMomentOneEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenSineMomentTwoEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenSineMomentThreeEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenSineMomentFourEnclosure
import ArithmeticHodge.Analysis.YoshidaEvenSineMomentFiveEnclosure
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
import ArithmeticHodge.Analysis.YoshidaClippedCriticalForm
import ArithmeticHodge.Analysis.YoshidaClippedLowModes
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticPolarBound
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticReality
import ArithmeticHodge.Analysis.MultiplicativeWeilSmallSupportPositivity
import ArithmeticHodge.Analysis.MultiplicativeWeilRestrictedSupportEndpointPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhysicalSymbol
import ArithmeticHodge.Analysis.YoshidaFactorTwoCenteredPhysical
import ArithmeticHodge.Analysis.YoshidaFactorTwoDiagonalPhysical
import ArithmeticHodge.Analysis.YoshidaFactorTwoParityDeterminant
import ArithmeticHodge.Analysis.YoshidaFactorTwoParityRealification
import ArithmeticHodge.Analysis.YoshidaFactorTwoCoreReduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoRealChannel
import ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeDomination
import ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeOverlap
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointClean
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointBilinear
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointParityPencil
import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointChannelRadius
import ArithmeticHodge.Analysis.EndpointCarleman
import ArithmeticHodge.Analysis.EndpointParityCarleman
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularSquare
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSquareAssembly
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseProduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRankLimit
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddSymmetricBound
import ArithmeticHodge.Analysis.YoshidaFactorTwoLaplaceModes
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAlternatingCoercivity
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCarleman
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRadiusClosure
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDirectionalTail
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedLow
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealification
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedTail
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedTailCoerciveStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointTailMixedCauchyStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointTailBilinearContinuityStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousProfileLinearStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousCleanPolarizationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedDecomposition
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddRealDecomposition
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointAdaptedReduction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLowSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowMatrix
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanEvenMatrix
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanEvenMomentFormula
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanOddMatrix
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteCleanOddPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowPhaseMatrix
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowDiskSchur
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEvenPerturbationAdaptation
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteEvenPerturbationFormula
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteOddPerturbationFormula
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteAlternatingFormula
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcretePerturbationMoments
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationMomentSeries
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineCosSeries
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationOneSubCosSeries
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationAffineSinSeries
import ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeTrigEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationConstantEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoCleanHighSineEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowToeplitz
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitToeplitz
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseConcreteLowSplitCertificate
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCleanPolarizationCritical
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseStructuralLowData
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseStructuralReserve
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixUnbalancedDiskCertificateStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOperatorContraction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseRemainderClosure
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseAdversarialWitness
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddRawGap
import ArithmeticHodge.Analysis.YoshidaFactorTwoCoreExplicitObstruction
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
import ArithmeticHodge.Analysis.YoshidaWeightedTailBounds
import ArithmeticHodge.Analysis.YoshidaTZeroTailBounds
import ArithmeticHodge.Analysis.YoshidaCoercivityNumerics
import ArithmeticHodge.Analysis.YoshidaConstantBounds
import ArithmeticHodge.Analysis.YoshidaSectionSixAnalytic
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
