import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseTailRealImagStructural
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false

open Complex Real
open scoped InnerProductSpace

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural

noncomputable section

open ArithmeticHodge.Analysis
open FormSpace
open YoshidaSectionSixAnalytic
open YoshidaCoercivityNumerics
open YoshidaEndpointEvenBoundaryProductionBridge
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaEvenHomogeneousCoercivity
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoEndpointClean
open YoshidaFactorTwoPhaseBoundaryContinuousDecompositionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousReductionStructural
open YoshidaFactorTwoPhaseBoundaryContinuousTailStructural
open YoshidaFactorTwoPhaseOddRealDecomposition
open YoshidaFactorTwoPhaseTailRealImagStructural
open YoshidaOddHomogeneousCoercivity
open YoshidaWeightedTailBounds

/-!
# Critical norm of the canonical complex phase-tail core

The algebraic phase carrier is the `L²` product of the even and odd
critical-form spaces.  Its pointwise real and imaginary tail coordinates feed
the real phase pencil.  The main identity below says that the complex Hilbert
norm is exactly `yoshidaA` times the sum of the two clean real diagonals.
-/

abbrev EvenPhaseTailFormSpace :=
  FormSpace evenOneNinetyNineTailPositiveHermitianForm

abbrev OddPhaseTailFormSpace :=
  FormSpace oddTenTailPositiveHermitianForm

abbrev CanonicalPhaseTailCore :=
  WithLp 2 (EvenPhaseTailFormSpace × OddPhaseTailFormSpace)

/-- Boundary-continuous even profile of the real coordinate. -/
def canonicalPhaseTailEvenRealProfile
    (x : CanonicalPhaseTailCore) : ℝ → ℝ :=
  boundaryCanonicalEvenTailProfile (evenTailRealPart x.fst.toV)

/-- Boundary-continuous even profile of the imaginary coordinate. -/
def canonicalPhaseTailEvenImagProfile
    (x : CanonicalPhaseTailCore) : ℝ → ℝ :=
  boundaryCanonicalEvenTailProfile (evenTailImagPart x.fst.toV)

/-- Centered odd profile of the real coordinate. -/
def canonicalPhaseTailOddRealProfile
    (x : CanonicalPhaseTailCore) : ℝ → ℝ :=
  canonicalOddTailProfile (oddTailRealPart x.snd.toV)

/-- Centered odd profile of the imaginary coordinate. -/
def canonicalPhaseTailOddImagProfile
    (x : CanonicalPhaseTailCore) : ℝ → ℝ :=
  canonicalOddTailProfile (oddTailImagPart x.snd.toV)

/-- The critical norm of a pointwise-real standard even tail is exactly the
clean energy of its boundary-continuous representative. -/
theorem evenRealTailFormSpace_norm_sq_eq_clean
    (f : YoshidaEvenOneNinetyNineTail)
    (hreal : ∀ x : ℝ,
      (evenOneNinetyNineTailToClippedSmooth f x).im = 0) :
    ‖(FormSpace.of f : EvenPhaseTailFormSpace)‖ ^ 2 =
      yoshidaA * yoshidaEndpointOddCleanQuadratic
        (boundaryCanonicalEvenTailProfile f) := by
  rw [FormSpace.norm_sq_eq_form_re]
  let p := canonicalEvenTailPointwise f
  have hbridge := clippedCriticalFormValue_even_eq_clean_add_boundary
    p (by simpa only [p, canonicalEvenTailPointwise] using hreal)
  change clippedCriticalFormValue yoshidaA yoshidaA_pos
      (evenOneNinetyNineTailToClippedSmooth f) =
    yoshidaA * yoshidaEndpointOddCleanQuadratic
      (boundaryCanonicalEvenTailProfile f) at hbridge
  simpa only [clippedCriticalFormValue,
    evenOneNinetyNineTailCriticalForm_apply] using hbridge

/-- The critical norm of a pointwise-real standard odd tail is exactly its
clean centered energy. -/
theorem oddRealTailFormSpace_norm_sq_eq_clean
    (f : YoshidaOddTenTail)
    (hreal : ∀ x : ℝ, (oddTenTailToClippedSmooth f x).im = 0) :
    ‖(FormSpace.of f : OddPhaseTailFormSpace)‖ ^ 2 =
      yoshidaA * yoshidaEndpointOddCleanQuadratic
        (canonicalOddTailProfile f) := by
  rw [FormSpace.norm_sq_eq_form_re]
  obtain ⟨hneg, hpos⟩ := oddTenTail_endpoints_zero f
  have hbridge :=
    clippedCriticalFormValue_eq_endpoint_mul_clean_of_real_endpoints_zero
      (f : YoshidaClippedPeriodicCore yoshidaA) hreal hneg hpos
  change clippedCriticalFormValue yoshidaA yoshidaA_pos
      (oddTenTailToClippedSmooth f) =
    yoshidaA * yoshidaEndpointOddCleanQuadratic
      (canonicalOddTailProfile f) at hbridge
  simpa only [clippedCriticalFormValue, oddTenTailCriticalForm_apply]
    using hbridge

/-- Exact Pythagorean clean-coordinate formula for the full complex
canonical phase-tail core. -/
theorem canonicalPhaseTailCore_norm_sq_eq_clean_real_add_imag
    (x : CanonicalPhaseTailCore) :
    ‖x‖ ^ 2 = yoshidaA *
      (factorTwoEndpointChannelCleanSum
          (canonicalPhaseTailEvenRealProfile x)
          (canonicalPhaseTailOddRealProfile x) +
       factorTwoEndpointChannelCleanSum
          (canonicalPhaseTailEvenImagProfile x)
          (canonicalPhaseTailOddImagProfile x)) := by
  rw [WithLp.prod_norm_sq_eq_of_L2,
    evenFormSpace_norm_sq_eq_real_add_imag,
    oddFormSpace_norm_sq_eq_real_add_imag,
    evenRealTailFormSpace_norm_sq_eq_clean
      (evenTailRealPart x.fst.toV) (by
        intro t
        change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).re :
          ℝ) : ℂ)).im) = 0
        simp),
    evenRealTailFormSpace_norm_sq_eq_clean
      (evenTailImagPart x.fst.toV) (by
        intro t
        change (((((evenOneNinetyNineTailToClippedSmooth x.fst.toV t).im :
          ℝ) : ℂ)).im) = 0
        simp),
    oddRealTailFormSpace_norm_sq_eq_clean
      (oddTailRealPart x.snd.toV) (by
        intro t
        change (((((oddTenTailToClippedSmooth x.snd.toV t).re :
          ℝ) : ℂ)).im) = 0
        simp),
    oddRealTailFormSpace_norm_sq_eq_clean
      (oddTailImagPart x.snd.toV) (by
        intro t
        change (((((oddTenTailToClippedSmooth x.snd.toV t).im :
          ℝ) : ℂ)).im) = 0
        simp)]
  unfold factorTwoEndpointChannelCleanSum
    canonicalPhaseTailEvenRealProfile canonicalPhaseTailEvenImagProfile
    canonicalPhaseTailOddRealProfile canonicalPhaseTailOddImagProfile
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCanonicalTailCoreNormStructural
