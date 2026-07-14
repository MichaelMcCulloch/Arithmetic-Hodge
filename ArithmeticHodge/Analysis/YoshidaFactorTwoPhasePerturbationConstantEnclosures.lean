import ArithmeticHodge.Analysis.RationalIntervalWidth
import ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeTrigEnclosures

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationConstantEnclosures

noncomputable section

open RatInterval
open YoshidaFactorTwoCenteredPhysical
open YoshidaEndpointHyperbolicBound
open YoshidaFactorTwoPhasePerturbationMomentSeries
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaSineMomentEnclosures

/-!
# Fine constants for factor-two perturbation enclosures

The four scalar perturbation families share the same small collection of
transcendental coefficients.  This module encloses them once on a fine
rational grid, leaving downstream moment files to concentrate on their
dyadic series.
-/

/-- A `10^-15` rational enclosure of `sqrt 3`. -/
def factorTwoPrimeSqrtThreeInterval : RatInterval :=
  ⟨1732050807568877 / 1000000000000000,
    1732050807568878 / 1000000000000000⟩

theorem factorTwoPrimeSqrtThreeInterval_contains :
    factorTwoPrimeSqrtThreeInterval.Contains (Real.sqrt 3) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs0 := Real.sqrt_nonneg 3
  constructor <;>
    norm_num [factorTwoPrimeSqrtThreeInterval, Contains] <;> nlinarith

/-- `log 3 = log 2 + log (3/2)`, using the two fine logarithm boxes already
needed for phase reduction. -/
def factorTwoPrimeLogThreeInterval : RatInterval :=
  factorTwoPrimeLogTwoInterval + factorTwoPrimeShiftInterval

theorem factorTwoPrimeLogThreeInterval_contains :
    factorTwoPrimeLogThreeInterval.Contains (Real.log 3) := by
  have h := contains_add factorTwoPrimeLogTwoInterval_contains
    factorTwoPrimeShiftInterval_contains
  have hlog : Real.log (3 : ℝ) =
      Real.log 2 + Real.log (3 / 2 : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  unfold factorTwoPrimeLogThreeInterval
  convert h using 1
  rw [hlog]
  unfold factorTwoMomentLength yoshidaEndpointA factorTwoPrimeShift
  ring

/-- Fine enclosure of the retained-prime coefficient `log 3 / sqrt 3`. -/
def factorTwoPrimeBetaInterval : RatInterval :=
  factorTwoPrimeLogThreeInterval / factorTwoPrimeSqrtThreeInterval

theorem factorTwoPrimeBetaInterval_contains :
    factorTwoPrimeBetaInterval.Contains (Real.log 3 / Real.sqrt 3) := by
  exact contains_div_of_pos
    (by norm_num [factorTwoPrimeSqrtThreeInterval])
    factorTwoPrimeLogThreeInterval_contains
    factorTwoPrimeSqrtThreeInterval_contains

/-- Fine enclosure of the affine retained-prime height
`2 - 2 log(3/2) / log 2`. -/
def factorTwoPrimeAffineHeightInterval : RatInterval :=
  pure 2 - pure 2 * factorTwoPrimeShiftInterval /
    factorTwoPrimeLogTwoInterval

theorem factorTwoPrimeAffineHeightInterval_contains :
    factorTwoPrimeAffineHeightInterval.Contains
      (2 - 2 * factorTwoPrimeShift / factorTwoMomentLength) := by
  have hratio := contains_div_of_pos
    (I := pure 2 * factorTwoPrimeShiftInterval)
    (J := factorTwoPrimeLogTwoInterval)
    (by norm_num [factorTwoPrimeLogTwoInterval])
    (contains_mul (contains_pure 2) factorTwoPrimeShiftInterval_contains)
    factorTwoPrimeLogTwoInterval_contains
  exact contains_sub (contains_pure 2) hratio

/-- Fine interval expression for the growing-head defect `(sqrt 2 - 1)^2`. -/
def factorTwoHeadDefectInterval : RatInterval :=
  (sqrtTwoInterval - pure 1) * (sqrtTwoInterval - pure 1)

theorem factorTwoHeadDefectInterval_contains :
    factorTwoHeadDefectInterval.Contains factorTwoHeadDefect := by
  have hsub := contains_sub sqrtTwoInterval_contains
    (contains_pure (1 : ℚ))
  have hsub' : (sqrtTwoInterval - pure 1).Contains
      (Real.sqrt 2 - 1) := by
    simpa using hsub
  unfold factorTwoHeadDefectInterval factorTwoHeadDefect
  rw [pow_two]
  exact contains_mul hsub' hsub'

/-- The shared coefficient boxes are much narrower than the `10^-9` scalar
moment budget. -/
theorem factorTwoPerturbationConstantIntervals_width_le :
    width factorTwoPrimeBetaInterval ≤ (1 / 10000000000000 : ℚ) ∧
      width factorTwoPrimeAffineHeightInterval ≤
        (1 / 1000000000000 : ℚ) ∧
      width factorTwoHeadDefectInterval ≤
        (1 / 100000000000000 : ℚ) := by
  decide +kernel

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhasePerturbationConstantEnclosures
