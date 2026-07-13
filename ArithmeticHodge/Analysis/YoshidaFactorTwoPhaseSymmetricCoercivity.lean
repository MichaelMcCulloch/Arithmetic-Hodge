import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEnvelope
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailCoercivity

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity

noncomputable section

open CenteredEndpointCorrelation
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointSingularCorrelation
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseTailCoercivity

/-!
# The symmetric factor-two phase coordinate

This file isolates the actual one-profile quadratic coordinate.  In
particular, the reflected endpoint pole is kept with its sign; replacing it
by an absolute-value envelope would introduce the logarithmic endpoint
potential and lose the desired mass-only constant.
-/

/-- Exact signed normal form of the symmetric perturbation. -/
theorem symmetricPerturbation_eq_regular_sub_pole_sub_primes
    (w : ℝ → ℝ) (hw : Continuous w) :
    factorTwoCenteredSymmetricPerturbation w =
        yoshidaEndpointA *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredForwardPhaseKernel w 0 1 0 t) +
          (∫ t : ℝ in 0..2,
            factorTwoCenteredReflectedDesingularizedPhaseKernel
              w 0 1 0 t) -
          (1 / 2 : ℝ) *
            (∫ t : ℝ in 0..2,
              factorTwoCenteredPhaseCorrelation w 0 1 0 t / (2 - t)) -
          (Real.log 2 / Real.sqrt 2) *
            (∫ x : ℝ in -1..1, w x ^ 2) -
          (Real.log 3 / Real.sqrt 3) *
            factorTwoCenteredPhaseCorrelation w 0 1 0
              (factorTwoPrimeShift / yoshidaEndpointA) := by
  have h :=
    phase_symmetric_add_alternating_eq_regular_sub_pole_sub_primes
      w 0 hw continuous_zero 1 0
  have hz : factorTwoCenteredSymmetricPerturbation (0 : ℝ → ℝ) = 0 := by
    simp [factorTwoCenteredSymmetricPerturbation,
      centeredEndpointCorrelation]
  simpa [hz] using h

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSymmetricCoercivity
