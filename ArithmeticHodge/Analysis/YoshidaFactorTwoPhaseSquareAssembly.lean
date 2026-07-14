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

/-- The smooth, scalar-mass, and retained-prime remainder left after the
reflected pole has been absorbed into the exact singular square. -/
def factorTwoPhaseSignedRemainder
    (u v : ℝ → ℝ) (a b : ℝ) : ℝ :=
  -(yoshidaEndpointScalarMassLoss + Real.log 2 +
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
        (factorTwoPrimeShift / yoshidaEndpointA)

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

/-- A unit production phase may be doubled inside the endpoint square while
only half of the clean quadratic is spent.  The exact radius-two square then
leaves half of the original clean coercivity available to control the signed
smooth/prime remainder. -/
theorem half_clean_add_half_radiusTwo_signedRemainder_le_endpointPhaseForm
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hlocalu : LocallyLipschitzOn (Icc (-1) 1) u)
    (hlocalv : LocallyLipschitzOn (Icc (-1) 1) v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 2 : ℝ) * factorTwoEndpointChannelCleanSum u v +
        (1 / 2 : ℝ) *
          factorTwoPhaseSignedRemainder u v (2 * a) (2 * b) ≤
      factorTwoEndpointChannelCleanSum u v +
        a * factorTwoEndpointChannelSymmetricSum u v +
        b * factorTwoCenteredAlternatingCoupling u v := by
  have hphase := endpointPhaseForm_eq_singularSquare_add_signedRemainder
    u v hu hv hlocalu hlocalv (2 * a) (2 * b)
  have hradius : (2 * a) ^ 2 + (2 * b) ^ 2 ≤ (4 : ℝ) := by
    nlinarith
  have hsquare :=
    integral_factorTwoPhaseSingularSquareNumerator_div_nonneg_of_sq_add_sq_le_four
      u v (2 * a) (2 * b) hradius
  have hremainder :
      factorTwoPhaseSignedRemainder u v (2 * a) (2 * b) ≤
        factorTwoEndpointChannelCleanSum u v +
          (2 * a) * factorTwoEndpointChannelSymmetricSum u v +
          (2 * b) * factorTwoCenteredAlternatingCoupling u v := by
    rw [hphase]
    dsimp only [factorTwoPhaseSignedRemainder]
    nlinarith
  nlinarith

/-- Quantitative radius-two decomposition retaining the raw logarithmic
reserve.  Doubling a unit production phase spends half of the clean
quadratic, but the doubled singular square still contains the full
positive-distance energy, yielding the additional `1/8` raw-energy terms. -/
theorem half_clean_add_eighth_raw_add_half_radiusTwo_remainder_le
    (u v : ℝ → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hlocalu : LocallyLipschitzOn (Icc (-1) 1) u)
    (hlocalv : LocallyLipschitzOn (Icc (-1) 1) v)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (1 / 2 : ℝ) * factorTwoEndpointChannelCleanSum u v +
        centeredRawLogEnergy u / 8 + centeredRawLogEnergy v / 8 +
        (1 / 2 : ℝ) *
          factorTwoPhaseSignedRemainder u v (2 * a) (2 * b) ≤
      factorTwoEndpointChannelCleanSum u v +
        a * factorTwoEndpointChannelSymmetricSum u v +
        b * factorTwoCenteredAlternatingCoupling u v := by
  have hphase := endpointPhaseForm_eq_singularSquare_add_signedRemainder
    u v hu hv hlocalu hlocalv (2 * a) (2 * b)
  have hphase' : factorTwoEndpointChannelCleanSum u v +
        (2 * a) * factorTwoEndpointChannelSymmetricSum u v +
        (2 * b) * factorTwoCenteredAlternatingCoupling u v =
      (1 / 2 : ℝ) *
          (∫ r : ℝ in 0..2,
            factorTwoPhaseSingularSquareNumerator
              u v (2 * a) (2 * b) r / r) +
        factorTwoPhaseSignedRemainder u v (2 * a) (2 * b) := by
    rw [hphase]
    unfold factorTwoPhaseSignedRemainder
    ring
  have hradius : (2 * a) ^ 2 + (2 * b) ^ 2 ≤ (4 : ℝ) := by
    nlinarith
  have hraw := half_raw_add_half_raw_le_singularSquareIntegral
    u v hu hv hlocalu hlocalv (2 * a) (2 * b) hradius
  calc
    (1 / 2 : ℝ) * factorTwoEndpointChannelCleanSum u v +
          centeredRawLogEnergy u / 8 + centeredRawLogEnergy v / 8 +
          (1 / 2 : ℝ) *
            factorTwoPhaseSignedRemainder u v (2 * a) (2 * b) ≤
        (1 / 2 : ℝ) * factorTwoEndpointChannelCleanSum u v +
          (1 / 4 : ℝ) *
            (∫ r : ℝ in 0..2,
              factorTwoPhaseSingularSquareNumerator
                u v (2 * a) (2 * b) r / r) +
          (1 / 2 : ℝ) *
            factorTwoPhaseSignedRemainder u v (2 * a) (2 * b) := by
      nlinarith
    _ = (1 / 2 : ℝ) * factorTwoEndpointChannelCleanSum u v +
          (1 / 2 : ℝ) *
            (factorTwoEndpointChannelCleanSum u v +
              (2 * a) * factorTwoEndpointChannelSymmetricSum u v +
              (2 * b) * factorTwoCenteredAlternatingCoupling u v) := by
      rw [hphase']
      ring
    _ = factorTwoEndpointChannelCleanSum u v +
          a * factorTwoEndpointChannelSymmetricSum u v +
          b * factorTwoCenteredAlternatingCoupling u v := by ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseSquareAssembly
