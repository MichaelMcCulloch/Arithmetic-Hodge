import ArithmeticHodge.Analysis.CoerciveBilinearSchurCharacterization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailBoundaryReductionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseDiskBoundaryStructural

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailPhysicalCharacterizationStructural

noncomputable section

open ArithmeticHodge.Analysis
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyClosureStructural
open YoshidaFactorTwoPhaseCanonicalLowTailAssemblyStructural
open YoshidaFactorTwoPhaseBoundaryCanonicalLowProfileStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionEnergyStructural
open YoshidaFactorTwoPhaseCanonicalLowTailBoundaryReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailCorrectionReductionStructural
open YoshidaFactorTwoPhaseCanonicalLowTailFunctionalStructural
open YoshidaFactorTwoPhaseCanonicalLowTailSchurStructural
open YoshidaFactorTwoPhaseCanonicalTailBilinearStructural
open YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseConcreteLowMatrix
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoPhaseDiskBoundaryStructural
open YoshidaFactorTwoPhaseFullProfile

local instance : InnerProductSpace ℝ CanonicalPhaseTailCore :=
  InnerProductSpace.rclikeToReal ℂ CanonicalPhaseTailCore

/-!
# Exact physical characterization of the canonical Schur certificate

The corrected low Gram is not merely a sufficient certificate.  At a fixed
phase it is positive semidefinite exactly when the original coupled low--tail
quadratic is nonnegative on the whole completed tail space.
-/

/-- Exact completed-space characterization of the reduced canonical Schur
certificate. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_full_nonneg
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) ↔
      ∀ (c : FactorTwoPhaseLowIndex → ℝ)
          (z : CanonicalPhaseTailCompletion),
        0 ≤ c ⬝ᵥ (canonicalPhaseLowMatrix a b *ᵥ c) +
          2 * ∑ k, c k *
            completedCanonicalPhaseLowBasisTailRealFunctional
              k a b hphase z +
          completedCanonicalPhaseTailBilinear a b hphase z z := by
  change Matrix.PosSemidef
      (coerciveBilinearCorrectedGram
        (canonicalPhaseLowMatrix a b)
        (completedCanonicalPhaseTailBilinear a b hphase)
        (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
        (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
          k a b hphase)) ↔ _
  exact coerciveBilinearCorrectedGram_posSemidef_iff_full_nonneg
    (canonicalPhaseLowMatrix a b)
    (completedCanonicalPhaseTailBilinear a b hphase)
    (completedCanonicalPhaseTailBilinear_isCoercive a b hphase)
    (fun k ↦ completedCanonicalPhaseLowBasisTailRealFunctional
      k a b hphase)
    (canonicalPhaseLowMatrix_isHermitian a b)
    (completedCanonicalPhaseTailBilinear_symm a b hphase)

/-- The reduced corrected Gram is positive semidefinite exactly when every
literal canonical profile with one real low coordinate and an arbitrary
complex tail has nonnegative phase value.  Thus failure of this Schur
certificate is witnessed on the dense physical tail core; it is not an
artifact of completing the tail space. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_physical_nonneg
    (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1) :
    Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase) ↔
      ∀ (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore),
        CanonicalPhasePhysicalLowTailNonnegative c 0 x a b := by
  constructor
  · intro hG c x
    exact canonicalPhasePhysicalLowTailValue_nonneg_of_realCorrectedGram_posSemidef
      c 0 x a b hphase hG
  · intro hphysical
    apply
      (completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_full_nonneg
        a b hphase).2
    intro c z
    refine UniformSpace.Completion.induction_on z
      (isClosed_le (by fun_prop) (by fun_prop)) ?_
    intro x
    have h := hphysical c x
    unfold CanonicalPhasePhysicalLowTailNonnegative at h
    have hassembly := canonicalPhasePhysicalLowTailValue_eq_schurQuadratic
      c 0 x a b hphase
    unfold CanonicalPhasePhysicalLowTailAssembly at hassembly
    rw [hassembly] at h
    unfold canonicalPhaseLowTailSchurQuadratic at h
    dsimp only at h
    rw [canonicalPhaseLowRealImagMatrix_quadratic,
      completedCanonicalPhaseLowRealImagFunctional_sum] at h
    simpa only [zero_dotProduct, Pi.zero_apply, zero_mul,
      Finset.sum_const_zero, add_zero] using h

/-- Clean center of the literal canonical complex low--tail profile. -/
def canonicalPhasePhysicalLowTailCleanSum
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) : ℝ :=
  factorTwoEndpointChannelCleanSum
      (factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients cReal) +
        canonicalPhaseTailEvenRealProfile x)
      (factorTwoOddLowSynthesis
          (canonicalPhaseLowOddCoefficients cReal) +
        canonicalPhaseTailOddRealProfile x) +
    factorTwoEndpointChannelCleanSum
      (factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients cImag) +
        canonicalPhaseTailEvenImagProfile x)
      (factorTwoOddLowSynthesis
          (canonicalPhaseLowOddCoefficients cImag) +
        canonicalPhaseTailOddImagProfile x)

/-- Complex symmetric/alternating coordinate of the literal canonical
complex low--tail profile.  The two real-coordinate channel values are added
before taking the norm, so this retains the sharp compensation between them. -/
def canonicalPhasePhysicalLowTailCoordinate
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) : ℂ :=
  factorTwoEndpointChannelCoordinate
      (factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients cReal) +
        canonicalPhaseTailEvenRealProfile x)
      (factorTwoOddLowSynthesis
          (canonicalPhaseLowOddCoefficients cReal) +
        canonicalPhaseTailOddRealProfile x) +
    factorTwoEndpointChannelCoordinate
      (factorTwoBoundaryCanonicalEvenLowProfile
          (canonicalPhaseLowEvenCoefficients cImag) +
        canonicalPhaseTailEvenImagProfile x)
      (factorTwoOddLowSynthesis
          (canonicalPhaseLowOddCoefficients cImag) +
        canonicalPhaseTailOddImagProfile x)

/-- The physical canonical phase is the affine scalar pairing with its one
sharp complex coordinate. -/
theorem canonicalPhasePhysicalLowTailValue_eq_clean_add_coordinate
    (cReal cImag : FactorTwoPhaseLowIndex → ℝ)
    (x : CanonicalPhaseTailCore) (a b : ℝ) :
    canonicalPhasePhysicalLowTailValue cReal cImag x a b =
      canonicalPhasePhysicalLowTailCleanSum cReal cImag x +
        a * (canonicalPhasePhysicalLowTailCoordinate cReal cImag x).re +
        b * (canonicalPhasePhysicalLowTailCoordinate cReal cImag x).im := by
  unfold canonicalPhasePhysicalLowTailValue
    canonicalPhasePhysicalLowTailCleanSum
    canonicalPhasePhysicalLowTailCoordinate
    factorTwoEndpointChannelPhase
    factorTwoEndpointChannelCoordinate
  simp only [Complex.add_re, Complex.add_im]
  ring

/-- Exact phase-free form of the remaining circle certificate.  Uniform
circle PSD of the reduced canonical Schur complement is equivalent to one
physical numerical-radius inequality for every retained low vector and every
canonical complex tail. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_circle_posSemidef_iff_physical_radius :
    (∀ (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1),
      a ^ 2 + b ^ 2 = 1 →
        Matrix.PosSemidef
          (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase)) ↔
      ∀ (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore),
        0 ≤ canonicalPhasePhysicalLowTailCleanSum c 0 x ∧
          Complex.normSq (canonicalPhasePhysicalLowTailCoordinate c 0 x) ≤
            canonicalPhasePhysicalLowTailCleanSum c 0 x ^ 2 := by
  constructor
  · intro hcircle c x
    have hradius := (real_unitCircle_phase_nonneg_iff_radius
        (canonicalPhasePhysicalLowTailCleanSum c 0 x)
        (canonicalPhasePhysicalLowTailCoordinate c 0 x).re
        (canonicalPhasePhysicalLowTailCoordinate c 0 x).im).1 (by
      intro a b hab
      have hphysical :=
        (completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_physical_nonneg
          a b hab.le).1 (hcircle a b hab.le hab) c x
      unfold CanonicalPhasePhysicalLowTailNonnegative at hphysical
      rwa [canonicalPhasePhysicalLowTailValue_eq_clean_add_coordinate]
        at hphysical)
    refine ⟨hradius.1, ?_⟩
    simpa only [Complex.normSq_apply, pow_two] using hradius.2
  · intro hradius a b hphase hab
    apply
      (completedCanonicalPhaseLowTailRealCorrectedGram_posSemidef_iff_physical_nonneg
        a b hphase).2
    intro c x
    unfold CanonicalPhasePhysicalLowTailNonnegative
    rw [canonicalPhasePhysicalLowTailValue_eq_clean_add_coordinate]
    have hradius' :
        0 ≤ canonicalPhasePhysicalLowTailCleanSum c 0 x ∧
          (canonicalPhasePhysicalLowTailCoordinate c 0 x).re ^ 2 +
              (canonicalPhasePhysicalLowTailCoordinate c 0 x).im ^ 2 ≤
            canonicalPhasePhysicalLowTailCleanSum c 0 x ^ 2 := by
      simpa only [Complex.normSq_apply, pow_two] using hradius c x
    exact (real_unitCircle_phase_nonneg_iff_radius
      (canonicalPhasePhysicalLowTailCleanSum c 0 x)
      (canonicalPhasePhysicalLowTailCoordinate c 0 x).re
      (canonicalPhasePhysicalLowTailCoordinate c 0 x).im).2
        hradius' a b hab

/-- Uniform PSD on the entire phase disk is equivalent to the same single
phase-free physical radius inequality.  The nontrivial circle-to-disk
direction is supplied by Loewner concavity of the Schur complement. -/
theorem completedCanonicalPhaseLowTailRealCorrectedGram_disk_posSemidef_iff_physical_radius :
    (∀ (a b : ℝ) (hphase : a ^ 2 + b ^ 2 ≤ 1),
      Matrix.PosSemidef
        (completedCanonicalPhaseLowTailRealCorrectedGram a b hphase)) ↔
      ∀ (c : FactorTwoPhaseLowIndex → ℝ) (x : CanonicalPhaseTailCore),
        0 ≤ canonicalPhasePhysicalLowTailCleanSum c 0 x ∧
          Complex.normSq (canonicalPhasePhysicalLowTailCoordinate c 0 x) ≤
            canonicalPhasePhysicalLowTailCleanSum c 0 x ^ 2 := by
  constructor
  · intro hdisk
    apply
      completedCanonicalPhaseLowTailRealCorrectedGram_circle_posSemidef_iff_physical_radius.mp
    intro a b hphase _hcircle
    exact hdisk a b hphase
  · intro hradius a b hphase
    apply completedCanonicalPhaseLowTailRealCorrectedGram_disk_posSemidef_of_circle
      ((completedCanonicalPhaseLowTailRealCorrectedGram_circle_posSemidef_iff_physical_radius).2
        hradius)
      a b hphase

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalLowTailPhysicalCharacterizationStructural
