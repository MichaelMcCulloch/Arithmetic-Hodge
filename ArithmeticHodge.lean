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
import ArithmeticHodge.Analysis.ThetaFunction
import ArithmeticHodge.Analysis.ZetaFunctionalEquation
import ArithmeticHodge.Analysis.WeilDefs
import ArithmeticHodge.Analysis.MultiplicativeWeil
import ArithmeticHodge.Analysis.MultiplicativeWeilTranspose
import ArithmeticHodge.Analysis.MultiplicativeWeilPrime
import ArithmeticHodge.Analysis.MultiplicativeWeilArchimedean
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadratic
import ArithmeticHodge.Analysis.MultiplicativeWeilQuadraticMellin
import ArithmeticHodge.Analysis.MultiplicativeWeilFunctional
import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
import ArithmeticHodge.Analysis.EntireFunction.MinimumModulus
import ArithmeticHodge.Analysis.EntireFunction.Order
import ArithmeticHodge.Analysis.EntireFunction.Hadamard
import ArithmeticHodge.Analysis.ZetaProduct
import ArithmeticHodge.Analysis.MultiplicativeWeilZeros
import ArithmeticHodge.Analysis.MultiplicativeWeilCriterion
import ArithmeticHodge.Analysis.MultiplicativeWeilMellinFourier
import ArithmeticHodge.Analysis.EntireFunction.CompletedZetaZeroExponent
import ArithmeticHodge.Analysis.ZetaZeroCount
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
