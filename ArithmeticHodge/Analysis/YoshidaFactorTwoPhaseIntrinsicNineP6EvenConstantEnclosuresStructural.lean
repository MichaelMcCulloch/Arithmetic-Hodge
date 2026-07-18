import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationGramStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationConstantEnclosures

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenConstantEnclosuresStructural

noncomputable section

open RatInterval
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenPerturbationGramStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural
open YoshidaFactorTwoPhasePerturbationConstantEnclosures
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaOddGramPrefix
open YoshidaSineMomentEnclosures

/-!
# Rational constants for the intrinsic even P6 endpoint certificate

The endpoint matrices depend on six scalar quantities.  This module encloses
the four quantities not already exposed directly by the perturbation-constant
API and records a reusable interval-power lemma.  All endpoints are exact
rationals; no floating-point evaluation enters these statements.
-/

/-- Fine enclosure of the endpoint half-length `log 2 / 2`. -/
def factorTwoP6EvenEndpointAInterval : RatInterval :=
  logTwoFineInterval / pure 2

theorem factorTwoP6EvenEndpointAInterval_contains :
    factorTwoP6EvenEndpointAInterval.Contains yoshidaEndpointA := by
  have h := contains_div_of_pos
    (I := logTwoFineInterval) (J := pure 2)
    (by norm_num [RatInterval.pure]) logTwoFineInterval_contains
      (contains_pure 2)
  simpa only [factorTwoP6EvenEndpointAInterval, yoshidaEndpointA,
    yoshidaLength] using h

/-- Fine enclosure of the scalar mass in the clean endpoint form. -/
def factorTwoP6EvenScalarMassInterval : RatInterval :=
  ⟨13554324 / 10000000, 13554329 / 10000000⟩

theorem factorTwoP6EvenScalarMassInterval_contains :
    factorTwoP6EvenScalarMassInterval.Contains
      yoshidaEndpointScalarMassLoss := by
  have h := plusP5_scalarMassLoss_fine_bounds
  norm_num [factorTwoP6EvenScalarMassInterval, Contains] at h ⊢
  exact ⟨h.1.le, h.2.le⟩

/-- Fine enclosure of the retained `p = 2` coefficient `log 2 / sqrt 2`. -/
def factorTwoP6EvenPrimeTwoCoefficientInterval : RatInterval :=
  logTwoFineInterval / sqrtTwoInterval

theorem factorTwoP6EvenPrimeTwoCoefficientInterval_contains :
    factorTwoP6EvenPrimeTwoCoefficientInterval.Contains
      (Real.log 2 / Real.sqrt 2) := by
  have h := contains_div_of_pos
    (I := logTwoFineInterval) (J := sqrtTwoInterval)
    (by norm_num [sqrtTwoInterval]) logTwoFineInterval_contains
      sqrtTwoInterval_contains
  simpa only [factorTwoP6EvenPrimeTwoCoefficientInterval,
    yoshidaLength] using h

/-- Fine enclosure of the normalized retained-prime height
`factorTwoPrimeShift / yoshidaEndpointA`. -/
def factorTwoP6EvenPrimeHeightInterval : RatInterval :=
  pure 2 - factorTwoPrimeAffineHeightInterval

theorem factorTwoP6EvenPrimeHeightInterval_contains :
    factorTwoP6EvenPrimeHeightInterval.Contains
      factorTwoP6EvenPrimeHeight := by
  have h := contains_sub (contains_pure 2)
    factorTwoPrimeAffineHeightInterval_contains
  have heq :
      2 - (2 - 2 * factorTwoPrimeShift / factorTwoMomentLength) =
        factorTwoP6EvenPrimeHeight := by
    unfold factorTwoP6EvenPrimeHeight factorTwoMomentLength
    field_simp [yoshidaEndpointA_pos.ne']
    ring
  unfold factorTwoP6EvenPrimeHeightInterval
  rw [← heq]
  exact h

/-- Repeated interval multiplication, used for the endpoint polynomials. -/
def factorTwoP6EvenIntervalPow (I : RatInterval) : ℕ → RatInterval
  | 0 => pure 1
  | n + 1 => factorTwoP6EvenIntervalPow I n * I

theorem factorTwoP6EvenIntervalPow_contains
    {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    ∀ n : ℕ, (factorTwoP6EvenIntervalPow I n).Contains (x ^ n) := by
  intro n
  induction n with
  | zero => simpa [factorTwoP6EvenIntervalPow] using contains_pure 1
  | succ n ih =>
      simpa only [factorTwoP6EvenIntervalPow, pow_succ] using
        contains_mul ih hx

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenConstantEnclosuresStructural
