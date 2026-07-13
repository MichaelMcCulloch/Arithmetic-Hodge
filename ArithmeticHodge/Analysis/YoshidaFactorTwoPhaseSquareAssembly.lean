import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointChannelRadius
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSingularSquare

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSquareAssembly

noncomputable section

open UnitIntervalLogEnergyAffine
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPotentialBound
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseSingularSquare
open YoshidaRegularKernelSchur

/-!
# Exact assembly of the factor-two phase square

The raw logarithmic energies, endpoint potentials, and reflected Cauchy pole
are kept together as the singular square proved in the preceding module.
This leaves an exact signed formula for the complete endpoint phase form;
no absolute-value envelope is used.
-/

/-- Canonical centered Bombieri profiles lie in the locally Lipschitz form
domain needed by the singular square identity. -/
theorem locallyLipschitzOn_factorTwoCenteredProfile
    (g : MultiplicativeWeil.BombieriTest) :
    LocallyLipschitzOn (Icc (-1) 1) (factorTwoCenteredProfile g) := by
  have hscale : ContDiff ℝ 1
      (fun x : ℝ ↦ yoshidaEndpointA * x) := by
    fun_prop
  have hpullback : ContDiff ℝ 1
      (fun x : ℝ ↦
        g.logarithmicPullbackSchwartz (1 / 2) (yoshidaEndpointA * x)) :=
    (g.logarithmicPullbackSchwartz (1 / 2)).smooth 1 |>.comp hscale
  have hprofile : ContDiff ℝ 1 (factorTwoCenteredProfile g) := by
    exact Complex.reCLM.contDiff.comp hpullback
  exact hprofile.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)

/-- Exact square-preserving normal form for the complete endpoint phase
channel.  The first term is manifestly nonnegative on the closed phase disk;
the remaining smooth, mass, and retained-prime terms stay signed. -/
theorem endpointPhaseForm_eq_singularSquare_add_signedRemainder
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hlocalu : LocallyLipschitzOn (Icc (-1) 1) u)
    (hlocalv : LocallyLipschitzOn (Icc (-1) 1) v)
    (a b : ℝ) :
    factorTwoEndpointChannelCleanSum u v +
          a * factorTwoEndpointChannelSymmetricSum u v +
          b * factorTwoCenteredAlternatingCoupling u v =
      (1 / 2 : ℝ) *
          (∫ r : ℝ in 0..2,
            factorTwoPhaseSingularSquareNumerator u v a b r / r) -
        (yoshidaEndpointScalarMassLoss + Real.log 2 +
            (Real.log 2 / Real.sqrt 2) * a) *
          ((∫ x : ℝ in -1..1, u x ^ 2) +
            ∫ x : ℝ in -1..1, v x ^ 2) -
        yoshidaEndpointA *
          ((yoshidaEndpointRegularQuadratic
              (fun x : ℝ ↦ (u x : ℂ))).re +
            (yoshidaEndpointRegularQuadratic
              (fun x : ℝ ↦ (v x : ℂ))).re) +
        (yoshidaEndpointHyperbolicQuadratic
            (fun x : ℝ ↦ (u x : ℂ)) +
          yoshidaEndpointHyperbolicQuadratic
            (fun x : ℝ ↦ (v x : ℂ))) +
        yoshidaEndpointA *
          (∫ t : ℝ in 0..2,
            factorTwoCenteredForwardPhaseKernel u v a b t) +
        (∫ t : ℝ in 0..2,
          factorTwoCenteredReflectedDesingularizedPhaseKernel u v a b t) -
        (Real.log 3 / Real.sqrt 3) *
          factorTwoCenteredPhaseCorrelation u v a b
            (factorTwoPrimeShift / yoshidaEndpointA) := by
  have hphase :=
    phase_symmetric_add_alternating_eq_regular_sub_pole_sub_primes
      u v hu hv a b
  have hsingular :=
    centeredEnergy_add_potential_add_logMass_sub_half_phasePole_eq_square
      u v hu hv hlocalu hlocalv a b
  rw [show factorTwoEndpointChannelCleanSum u v +
        a * factorTwoEndpointChannelSymmetricSum u v +
        b * factorTwoCenteredAlternatingCoupling u v =
      factorTwoEndpointChannelCleanSum u v +
        (a * (factorTwoCenteredSymmetricPerturbation u +
            factorTwoCenteredSymmetricPerturbation v) +
          b * factorTwoCenteredAlternatingCoupling u v) by
      unfold factorTwoEndpointChannelSymmetricSum
      ring,
    hphase]
  unfold factorTwoEndpointChannelCleanSum
    yoshidaEndpointOddCleanQuadratic
  rw [← hsingular]
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSquareAssembly
