import ArithmeticHodge.Analysis.UnitIntervalLogEnergyAffine
import ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialBound
import ArithmeticHodge.Analysis.YoshidaRegularKernelSchur
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddCleanPositive

open UnitIntervalLogEnergyAffine
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPotentialBound
open YoshidaRegularKernelSchur

noncomputable section

/-- Scalar mass loss in the clean centered endpoint expression. -/
def yoshidaEndpointScalarMassLoss : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.pi * Real.log 2)

/-- The generic clean centered endpoint quadratic.  The historical name is
retained for compatibility; parity enters only in subsequent positivity
theorems, not in this definition. -/
def yoshidaEndpointOddCleanQuadratic (w : ℝ → ℝ) : ℝ :=
  let f : ℝ → ℂ := fun x ↦ w x
  centeredRawLogEnergy w / 4 +
    (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) -
    yoshidaEndpointScalarMassLoss * (∫ x : ℝ in -1..1, w x ^ 2) -
    yoshidaEndpointA * (yoshidaEndpointRegularQuadratic f).re +
    yoshidaEndpointHyperbolicQuadratic f

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddCleanPositive
