import ArithmeticHodge.Analysis.YoshidaFactorTwoEndpointChannelRadius
import ArithmeticHodge.Analysis.TwoByTwoSchur

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile

noncomputable section

open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoEndpointParityPencil
open TwoByTwoSchur

/-!
# Exact full-profile low/tail phase decomposition

The proved directional estimate applies to the endpoint-zero Fourier tails.
For a general canonical profile, finite low modes and their cross terms with
the tail must be retained.  This module isolates those terms exactly: no
absolute-value estimate and no truncation is used.
-/

/-- Polarization of the clean endpoint quadratic.  This definition is useful
even before a closed analytic formula for the mixed clean term is chosen. -/
def factorTwoCenteredCleanPolarization
    (u v : ℝ → ℝ) : ℝ :=
  (yoshidaEndpointOddCleanQuadratic (u + v) -
      yoshidaEndpointOddCleanQuadratic u -
      yoshidaEndpointOddCleanQuadratic v) / 2

theorem yoshidaEndpointOddCleanQuadratic_add_eq_polarization
    (u v : ℝ → ℝ) :
    yoshidaEndpointOddCleanQuadratic (u + v) =
      yoshidaEndpointOddCleanQuadratic u +
        2 * factorTwoCenteredCleanPolarization u v +
      yoshidaEndpointOddCleanQuadratic v := by
  unfold factorTwoCenteredCleanPolarization
  ring

/-- The closed-disk phase form of one opposite-reflection-parity channel. -/
def factorTwoEndpointChannelPhase
    (u v : ℝ → ℝ) (a b : ℝ) : ℝ :=
  factorTwoEndpointChannelCleanSum u v +
    a * factorTwoEndpointChannelSymmetricSum u v +
    b * factorTwoCenteredAlternatingCoupling u v

/-- Every term involving at least one finite-low input after writing
`u = uLow + uTail` and `v = vLow + vTail`.  In particular, the three mixed
alternating terms and both clean/symmetric low-tail polarizations are kept. -/
def factorTwoEndpointLowTailCorrection
    (uLow uTail vLow vTail : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (yoshidaEndpointOddCleanQuadratic uLow +
      2 * factorTwoCenteredCleanPolarization uLow uTail +
    yoshidaEndpointOddCleanQuadratic vLow +
      2 * factorTwoCenteredCleanPolarization vLow vTail) +
  a * (factorTwoCenteredSymmetricPerturbation uLow +
      2 * factorTwoCenteredSymmetricPerturbationBilinear uLow uTail +
    factorTwoCenteredSymmetricPerturbation vLow +
      2 * factorTwoCenteredSymmetricPerturbationBilinear vLow vTail) +
  b * (factorTwoCenteredAlternatingCoupling uLow vLow +
    factorTwoCenteredAlternatingCoupling uLow vTail +
    factorTwoCenteredAlternatingCoupling uTail vLow)

/-- The genuinely mixed low--tail block of the channel phase.  This is the
quantity controlled by the sharp scalar Schur determinant, rather than by the
stronger and generally unnecessary sign condition on the whole correction. -/
def factorTwoEndpointLowTailMixed
    (uLow uTail vLow vTail : ℝ → ℝ) (a b : ℝ) : ℝ :=
  factorTwoCenteredCleanPolarization uLow uTail +
    factorTwoCenteredCleanPolarization vLow vTail +
  a * (factorTwoCenteredSymmetricPerturbationBilinear uLow uTail +
    factorTwoCenteredSymmetricPerturbationBilinear vLow vTail) +
  (b / 2) * (factorTwoCenteredAlternatingCoupling uLow vTail +
    factorTwoCenteredAlternatingCoupling uTail vLow)

/-- The retained correction is exactly its pure finite-low phase plus twice
the mixed low--tail block. -/
theorem factorTwoEndpointLowTailCorrection_eq_low_add_two_mixed
    (uLow uTail vLow vTail : ℝ → ℝ) (a b : ℝ) :
    factorTwoEndpointLowTailCorrection uLow uTail vLow vTail a b =
      factorTwoEndpointChannelPhase uLow vLow a b +
        2 * factorTwoEndpointLowTailMixed
          uLow uTail vLow vTail a b := by
  unfold factorTwoEndpointLowTailCorrection
    factorTwoEndpointChannelPhase factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum factorTwoEndpointLowTailMixed
  ring

/-- Exact channel decomposition into the already-controlled pure tail phase
and the complete finite-low/low-tail correction. -/
theorem factorTwoEndpointChannelPhase_add_add
    (uLow uTail vLow vTail : ℝ → ℝ)
    (huLow : Continuous uLow) (huTail : Continuous uTail)
    (hvLow : Continuous vLow) (hvTail : Continuous vTail)
    (a b : ℝ) :
    factorTwoEndpointChannelPhase
        (uLow + uTail) (vLow + vTail) a b =
      factorTwoEndpointChannelPhase uTail vTail a b +
        factorTwoEndpointLowTailCorrection
          uLow uTail vLow vTail a b := by
  unfold factorTwoEndpointChannelPhase
    factorTwoEndpointChannelCleanSum
    factorTwoEndpointChannelSymmetricSum
    factorTwoEndpointLowTailCorrection
  rw [yoshidaEndpointOddCleanQuadratic_add_eq_polarization,
    yoshidaEndpointOddCleanQuadratic_add_eq_polarization,
    factorTwoCenteredSymmetricPerturbation_add_eq_bilinear
      uLow uTail huLow huTail,
    factorTwoCenteredSymmetricPerturbation_add_eq_bilinear
      vLow vTail hvLow hvTail,
    factorTwoCenteredAlternatingCoupling_add_left
      uLow uTail (vLow + vTail) huLow huTail (hvLow.add hvTail),
    factorTwoCenteredAlternatingCoupling_add_right
      uLow vLow vTail huLow hvLow hvTail,
    factorTwoCenteredAlternatingCoupling_add_right
      uTail vLow vTail huTail hvLow hvTail]
  ring

/-- Exact low--mixed--tail decomposition of the full channel phase. -/
theorem factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    (uLow uTail vLow vTail : ℝ → ℝ)
    (huLow : Continuous uLow) (huTail : Continuous uTail)
    (hvLow : Continuous vLow) (hvTail : Continuous vTail)
    (a b : ℝ) :
    factorTwoEndpointChannelPhase
        (uLow + uTail) (vLow + vTail) a b =
      factorTwoEndpointChannelPhase uLow vLow a b +
        2 * factorTwoEndpointLowTailMixed
          uLow uTail vLow vTail a b +
      factorTwoEndpointChannelPhase uTail vTail a b := by
  rw [factorTwoEndpointChannelPhase_add_add
      uLow uTail vLow vTail huLow huTail hvLow hvTail,
    factorTwoEndpointLowTailCorrection_eq_low_add_two_mixed]
  ring

/-- Sharp block-Schur closure of the full profile.  Unlike the older
`correction ≥ 0` interface, this permits a negative mixed block up to its exact
determinant budget. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_low_tail_schur
    (uLow uTail vLow vTail : ℝ → ℝ)
    (huLow : Continuous uLow) (huTail : Continuous uTail)
    (hvLow : Continuous vLow) (hvTail : Continuous vTail)
    (a b : ℝ)
    (hLow : 0 ≤ factorTwoEndpointChannelPhase uLow vLow a b)
    (hTail : 0 ≤ factorTwoEndpointChannelPhase uTail vTail a b)
    (hSchur : factorTwoEndpointLowTailMixed
        uLow uTail vLow vTail a b ^ 2 ≤
      factorTwoEndpointChannelPhase uLow vLow a b *
        factorTwoEndpointChannelPhase uTail vTail a b) :
    0 ≤ factorTwoEndpointChannelPhase
      (uLow + uTail) (vLow + vTail) a b := by
  rw [factorTwoEndpointChannelPhase_add_add_eq_low_mixed_tail
    uLow uTail vLow vTail huLow huTail hvLow hvTail]
  exact scalar_low_tail_nonneg _ _ _ hLow hTail hSchur

/-- This is the exact remaining full-profile obligation: tail phase
nonnegativity plus nonnegativity of the retained low/cross correction imply
nonnegativity of the complete channel, with no loss in constants. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_tail_and_correction
    (uLow uTail vLow vTail : ℝ → ℝ)
    (huLow : Continuous uLow) (huTail : Continuous uTail)
    (hvLow : Continuous vLow) (hvTail : Continuous vTail)
    (a b : ℝ)
    (hTail : 0 ≤ factorTwoEndpointChannelPhase uTail vTail a b)
    (hCorrection : 0 ≤ factorTwoEndpointLowTailCorrection
      uLow uTail vLow vTail a b) :
    0 ≤ factorTwoEndpointChannelPhase
      (uLow + uTail) (vLow + vTail) a b := by
  rw [factorTwoEndpointChannelPhase_add_add
    uLow uTail vLow vTail huLow huTail hvLow hvTail]
  exact add_nonneg hTail hCorrection

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseFullProfile
