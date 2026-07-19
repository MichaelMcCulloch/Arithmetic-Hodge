import ArithmeticHodge.Analysis.YoshidaFourCellEvenStripCapacityStructural
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialEvenMomentStructural
import ArithmeticHodge.Analysis.YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
import ArithmeticHodge.Analysis.YoshidaFactorTwoPrimeTrigEnclosures
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenStripCapacityClosureStructural

noncomputable section

open YoshidaFourCellCompletedParityOperatorStructural
open YoshidaFourCellEvenStripCapacityStructural
open YoshidaFourCellOddEndpointStripCoercivityStructural
open YoshidaFourCellParityHalfFoldStructural
open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialEvenMomentStructural
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointSingularCorrelation
open YoshidaEndpointTriangleFoldLipschitz
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaFactorTwoIntegrableLagRepresenterStructural
open YoshidaFactorTwoPhaseIntrinsicOddP5CombinedNegativeProfileStructural
open YoshidaFactorTwoPrimeTrigEnclosures
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityOperatorStructural
open YoshidaFourCellRegularKernelSquareStructural
open YoshidaGeneralEndpointPhysicalRealQuadraticStructural
open YoshidaRegularKernelBound

/-!
# Exact obstruction to the even strip-capacity reduction

The strip-capacity lower operator differs from the completed even operator by
exactly the slack in the centered logarithmic spectral gap on the
reflection-even endpoint strip.  This file keeps that loss explicit and tests
it on a fixed low-degree even polynomial.
-/

private theorem integral_polynomial_thirteen
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
          a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 +
            a₁₁ * x ^ 11 + a₁₂ * x ^ 12 + a₁₃ * x ^ 13) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 +
                a₉ * (r ^ 10 - l ^ 10) / 10 +
                  a₁₀ * (r ^ 11 - l ^ 11) / 11 +
                    a₁₁ * (r ^ 12 - l ^ 12) / 12 +
                      a₁₂ * (r ^ 13 - l ^ 13) / 13 +
                        a₁₃ * (r ^ 14 - l ^ 14) / 14 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

private theorem integral_polynomial_nineteen
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ a₁₂ a₁₃ a₁₄ a₁₅ a₁₆ a₁₇ a₁₈ a₁₉
      l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 +
        a₄ * x ^ 4 + a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 +
          a₈ * x ^ 8 + a₉ * x ^ 9 + a₁₀ * x ^ 10 +
            a₁₁ * x ^ 11 + a₁₂ * x ^ 12 + a₁₃ * x ^ 13 +
              a₁₄ * x ^ 14 + a₁₅ * x ^ 15 + a₁₆ * x ^ 16 +
                a₁₇ * x ^ 17 + a₁₈ * x ^ 18 + a₁₉ * x ^ 19) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
                a₁₀ * (r ^ 11 - l ^ 11) / 11 +
                  a₁₁ * (r ^ 12 - l ^ 12) / 12 +
                    a₁₂ * (r ^ 13 - l ^ 13) / 13 +
                      a₁₃ * (r ^ 14 - l ^ 14) / 14 +
                        a₁₄ * (r ^ 15 - l ^ 15) / 15 +
                          a₁₅ * (r ^ 16 - l ^ 16) / 16 +
                            a₁₆ * (r ^ 17 - l ^ 17) / 17 +
                              a₁₇ * (r ^ 18 - l ^ 18) / 18 +
                                a₁₈ * (r ^ 19 - l ^ 19) / 19 +
                                  a₁₉ * (r ^ 20 - l ^ 20) / 20 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- The strip reduction subtracts exactly the unused part of the logarithmic
gap on the reflection-even strip. -/
theorem fourCellEvenStripCapacityLowerOperator_eq_completed_sub_gapSlack
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) :
    fourCellEvenStripCapacityLowerOperator w =
      fourCellEvenCompletedParityOperator w -
        ((1 / 2 : ℝ) * fourCellOddEndpointStripEvenRawEnergy w -
          2 * fourCellEvenEndpointStripResidualMass w) := by
  have hraw := fourCellOddEndpointStrip_rawEnergy_eq_even_add_odd w hw
  have hhalf := fourCellEndpointHalfMass_eq_evenMass_add_oddMass
    w hw.continuous
  have hevenMass := fourCellOddEndpointStripEvenMass_eq_mean_add_residual
    w hw.continuous
  unfold fourCellEvenStripCapacityLowerOperator
    fourCellEvenCompletedParityOperator
  rw [integral_fourCellEndpointHalfAntimatched_sq_eq_four_mul_oddMass,
    hhalf, hevenMass, hraw]
  ring

/-- A rational even sextic selected by the exact low-mode obstruction.  It
has a double zero at both endpoints. -/
def fourCellEvenStripWitness (x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ 2 * (3 - x ^ 2)

theorem fourCellEvenStripWitness_even :
    Function.Even fourCellEvenStripWitness := by
  intro x
  unfold fourCellEvenStripWitness
  ring

theorem fourCellEvenStripWitness_contDiff :
    ContDiff ℝ 1 fourCellEvenStripWitness := by
  unfold fourCellEvenStripWitness
  fun_prop

@[simp] theorem fourCellEvenStripWitness_neg_one :
    fourCellEvenStripWitness (-1) = 0 := by
  norm_num [fourCellEvenStripWitness]

@[simp] theorem fourCellEvenStripWitness_one :
    fourCellEvenStripWitness 1 = 0 := by
  norm_num [fourCellEvenStripWitness]

private theorem fourCellEvenStripWitness_nonneg
    {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    0 ≤ fourCellEvenStripWitness x := by
  unfold fourCellEvenStripWitness
  have hxSq : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2, sq_nonneg x]
  exact mul_nonneg (sq_nonneg _) (by linarith)

private theorem integral_zero_one_fourCellEvenStripWitness_sq :
    (∫ x : ℝ in 0..1, fourCellEvenStripWitness x ^ 2) =
      51712 / 15015 := by
  rw [show (fun x : ℝ ↦ fourCellEvenStripWitness x ^ 2) =
      fun x ↦
        9 * x ^ 0 + 0 * x ^ 1 + (-42) * x ^ 2 + 0 * x ^ 3 +
          79 * x ^ 4 + 0 * x ^ 5 + (-76) * x ^ 6 + 0 * x ^ 7 +
            39 * x ^ 8 + 0 * x ^ 9 + (-10) * x ^ 10 +
              0 * x ^ 11 + 1 * x ^ 12 + 0 * x ^ 13 by
    funext x
    unfold fourCellEvenStripWitness
    ring,
    integral_polynomial_thirteen]
  norm_num

private theorem integral_full_fourCellEvenStripWitness_sq :
    (∫ x : ℝ in -1..1, fourCellEvenStripWitness x ^ 2) =
      103424 / 15015 := by
  rw [show (fun x : ℝ ↦ fourCellEvenStripWitness x ^ 2) =
      fun x ↦
        9 * x ^ 0 + 0 * x ^ 1 + (-42) * x ^ 2 + 0 * x ^ 3 +
          79 * x ^ 4 + 0 * x ^ 5 + (-76) * x ^ 6 + 0 * x ^ 7 +
            39 * x ^ 8 + 0 * x ^ 9 + (-10) * x ^ 10 +
              0 * x ^ 11 + 1 * x ^ 12 + 0 * x ^ 13 by
    funext x
    unfold fourCellEvenStripWitness
    ring,
    integral_polynomial_thirteen]
  norm_num

private theorem fourCellEndpointPairing_fourCellEvenStripWitness :
    fourCellEndpointPairing fourCellEvenStripWitness =
      72358908928 / 3665771484375 := by
  unfold fourCellEndpointPairing
  rw [show (fun x : ℝ ↦
      fourCellEvenStripWitness x *
        fourCellEvenStripWitness (x - 8 / 5)) =
      fun x ↦
        (50193 / 15625) * x ^ 0 + (31824 / 3125) * x ^ 1 +
          (-1453242 / 15625) * x ^ 2 + (393744 / 3125) * x ^ 3 +
            (327131 / 3125) * x ^ 4 + (-189792 / 625) * x ^ 5 +
              (1362644 / 15625) * x ^ 6 + (559392 / 3125) * x ^ 7 +
                (-16437 / 125) * x ^ 8 + (-48 / 25) * x ^ 9 +
                  (142 / 5) * x ^ 10 + (-48 / 5) * x ^ 11 +
                    1 * x ^ 12 + 0 * x ^ 13 by
    funext x
    unfold fourCellEvenStripWitness
    ring,
    integral_polynomial_thirteen]
  norm_num

private theorem endpointPotential_fourCellEvenStripWitness_eq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * fourCellEvenStripWitness x ^ 2) =
      3448393856 / 676350675 -
        (103424 / 15015 : ℝ) * Real.log 2 := by
  have hInt (n : ℕ) : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ (2 * n))
      volume (-1) 1 := by
    have h := intervalIntegrable_endpointPotential_mul_sq
      (fun x : ℝ ↦ x ^ n) (continuous_id.pow n)
    apply h.congr
    intro x _hx
    ring
  have h0 := endpointPotentialEvenMoment_zero
  have h1 := endpointPotentialEvenMoment_succ 0
  have h2 := endpointPotentialEvenMoment_succ 1
  have h3 := endpointPotentialEvenMoment_succ 2
  have h4 := endpointPotentialEvenMoment_succ 3
  have h5 := endpointPotentialEvenMoment_succ 4
  have h6 := endpointPotentialEvenMoment_succ 5
  let hI0 := (hInt 0).const_mul 9
  let hI1 := (hInt 1).const_mul (-42)
  let hI2 := (hInt 2).const_mul 79
  let hI3 := (hInt 3).const_mul (-76)
  let hI4 := (hInt 4).const_mul 39
  let hI5 := (hInt 5).const_mul (-10)
  let hI6 := (hInt 6).const_mul 1
  let hI01 := hI0.add hI1
  let hI012 := hI01.add hI2
  let hI0123 := hI012.add hI3
  let hI01234 := hI0123.add hI4
  let hI012345 := hI01234.add hI5
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * fourCellEvenStripWitness x ^ 2) =
      fun x ↦
        9 * (yoshidaEndpointPotential x * x ^ (2 * 0)) +
          (-42) * (yoshidaEndpointPotential x * x ^ (2 * 1)) +
            79 * (yoshidaEndpointPotential x * x ^ (2 * 2)) +
              (-76) * (yoshidaEndpointPotential x * x ^ (2 * 3)) +
                39 * (yoshidaEndpointPotential x * x ^ (2 * 4)) +
                  (-10) * (yoshidaEndpointPotential x * x ^ (2 * 5)) +
                    1 * (yoshidaEndpointPotential x * x ^ (2 * 6)) by
    funext x
    unfold fourCellEvenStripWitness
    ring,
    intervalIntegral.integral_add hI012345 hI6,
    intervalIntegral.integral_add hI01234 hI5,
    intervalIntegral.integral_add hI0123 hI4,
    intervalIntegral.integral_add hI012 hI3,
    intervalIntegral.integral_add hI01 hI2,
    intervalIntegral.integral_add hI0 hI1]
  repeat rw [intervalIntegral.integral_const_mul]
  unfold endpointPotentialEvenMoment at h0 h1 h2 h3 h4 h5 h6
  norm_num at h0 h1 h2 h3 h4 h5 h6 ⊢
  linarith

private theorem centeredEndpointCorrelation_fourCellEvenStripWitness
    (t : ℝ) :
    centeredEndpointCorrelation fourCellEvenStripWitness t =
      103424 / 15015 - (2560 / 231 : ℝ) * t ^ 2 +
        (64 / 7 : ℝ) * t ^ 4 - (32 / 15 : ℝ) * t ^ 5 -
          (64 / 21 : ℝ) * t ^ 6 + (32 / 21 : ℝ) * t ^ 7 -
            (2 / 21 : ℝ) * t ^ 9 + (1 / 231 : ℝ) * t ^ 11 -
              (1 / 12012 : ℝ) * t ^ 13 := by
  unfold centeredEndpointCorrelation
  rw [show (fun x : ℝ ↦
      fourCellEvenStripWitness (t + x) * fourCellEvenStripWitness x) =
      fun x ↦
        (-3 * (t - 1) ^ 2 * (t + 1) ^ 2 * (t ^ 2 - 3)) * x ^ 0 +
          (-6 * t * (t - 1) * (t + 1) * (3 * t ^ 2 - 7)) * x ^ 1 +
            (7 * t ^ 6 - 80 * t ^ 4 + 139 * t ^ 2 - 42) * x ^ 2 +
              (2 * t * (t - 1) * (t + 1) * (21 * t ^ 2 - 79)) * x ^ 3 +
                (-5 * t ^ 6 + 130 * t ^ 4 - 290 * t ^ 2 + 79) * x ^ 4 +
                  (-6 * t * (5 * t ^ 4 - 40 * t ^ 2 + 38)) * x ^ 5 +
                    (t ^ 6 - 80 * t ^ 4 + 262 * t ^ 2 - 76) * x ^ 6 +
                      (6 * t * (t ^ 4 - 20 * t ^ 2 + 26)) * x ^ 7 +
                        (3 * (5 * t ^ 4 - 35 * t ^ 2 + 13)) * x ^ 8 +
                          (10 * t * (2 * t ^ 2 - 5)) * x ^ 9 +
                            (5 * (3 * t ^ 2 - 2)) * x ^ 10 +
                              (6 * t) * x ^ 11 + 1 * x ^ 12 + 0 * x ^ 13 by
    funext x
    unfold fourCellEvenStripWitness
    ring,
    integral_polynomial_thirteen]
  ring

private theorem centeredPositiveDistanceEnergy_fourCellEvenStripWitness
    (t : ℝ) :
    centeredPositiveDistanceEnergy fourCellEvenStripWitness t =
      t * (-(71 / 462 : ℝ) * t ^ 12 + 2 * t ^ 11 -
        (214 / 21 : ℝ) * t ^ 10 + 24 * t ^ 9 -
          (388 / 21 : ℝ) * t ^ 8 - 24 * t ^ 7 +
            (128 / 3 : ℝ) * t ^ 6 + (128 / 21 : ℝ) * t ^ 5 -
              (64 / 3 : ℝ) * t ^ 4 - (128 / 7 : ℝ) * t ^ 3 +
                (5120 / 231 : ℝ) * t) := by
  unfold centeredPositiveDistanceEnergy
  rw [show (fun x : ℝ ↦
      (fourCellEvenStripWitness (t + x) - fourCellEvenStripWitness x) ^ 2) =
      fun x ↦
        (t ^ 4 * (t ^ 4 - 5 * t ^ 2 + 7) ^ 2) * x ^ 0 +
          (4 * t ^ 3 * (t - 1) * (t + 1) * (3 * t ^ 2 - 7) *
            (t ^ 4 - 5 * t ^ 2 + 7)) * x ^ 1 +
          (2 * t ^ 2 * (33 * t ^ 8 - 225 * t ^ 6 + 539 * t ^ 4 -
            490 * t ^ 2 + 98)) * x ^ 2 +
          (20 * t ^ 3 * (t - 1) * (t + 1) *
            (11 * t ^ 4 - 49 * t ^ 2 + 56)) * x ^ 3 +
          (5 * t ^ 2 * (99 * t ^ 6 - 418 * t ^ 4 +
            494 * t ^ 2 - 112)) * x ^ 4 +
          (12 * t ^ 3 * (66 * t ^ 4 - 205 * t ^ 2 + 142)) * x ^ 5 +
          (2 * t ^ 2 * (461 * t ^ 4 - 970 * t ^ 2 + 284)) * x ^ 6 +
          (60 * t ^ 3 * (13 * t ^ 2 - 16)) * x ^ 7 +
          (15 * t ^ 2 * (31 * t ^ 2 - 16)) * x ^ 8 +
          (180 * t ^ 3) * x ^ 9 + (36 * t ^ 2) * x ^ 10 +
            0 * x ^ 11 + 0 * x ^ 12 + 0 * x ^ 13 by
    funext x
    unfold fourCellEvenStripWitness
    ring,
    integral_polynomial_thirteen]
  ring

private theorem centeredRawLogEnergy_fourCellEvenStripWitness :
    centeredRawLogEnergy fourCellEvenStripWitness = 1868288 / 135135 := by
  let Q : ℝ → ℝ := fun t ↦
    -(71 / 462 : ℝ) * t ^ 12 + 2 * t ^ 11 -
      (214 / 21 : ℝ) * t ^ 10 + 24 * t ^ 9 -
        (388 / 21 : ℝ) * t ^ 8 - 24 * t ^ 7 +
          (128 / 3 : ℝ) * t ^ 6 + (128 / 21 : ℝ) * t ^ 5 -
            (64 / 3 : ℝ) * t ^ 4 - (128 / 7 : ℝ) * t ^ 3 +
              (5120 / 231 : ℝ) * t
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      fourCellEvenStripWitness :=
    fourCellEvenStripWitness_contDiff.contDiffOn.locallyLipschitzOn
      (convex_Icc (-1) 1)
  have hfold :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      fourCellEvenStripWitness hlocal
  have hpoint (t : ℝ) :
      centeredPositiveDistanceEnergy fourCellEvenStripWitness t / t = Q t := by
    rw [centeredPositiveDistanceEnergy_fourCellEvenStripWitness]
    dsimp only [Q]
    by_cases ht : t = 0
    · simp [ht]
    · field_simp [ht]
  have hQ : (∫ t : ℝ in 0..2, Q t) = 934144 / 135135 := by
    rw [show Q = fun t : ℝ ↦
        0 * t ^ 0 + (5120 / 231) * t ^ 1 + 0 * t ^ 2 +
          (-128 / 7) * t ^ 3 + (-64 / 3) * t ^ 4 +
            (128 / 21) * t ^ 5 + (128 / 3) * t ^ 6 +
              (-24) * t ^ 7 + (-388 / 21) * t ^ 8 +
                24 * t ^ 9 + (-214 / 21) * t ^ 10 +
                  2 * t ^ 11 + (-71 / 462) * t ^ 12 + 0 * t ^ 13 by
      funext t
      dsimp only [Q]
      ring,
      integral_polynomial_thirteen]
    norm_num
  rw [show (fun t : ℝ ↦
      centeredPositiveDistanceEnergy fourCellEvenStripWitness t / t) = Q by
    funext t
    exact hpoint t, hQ] at hfold
  linarith

/-! ## Certified scalar and hyperbolic bounds -/

private theorem fine_log_two_bounds :
    (69314718055994 / 100000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (69314718055995 / 100000000000000 : ℝ) := by
  have hlog : factorTwoPrimeLogTwoInterval.Contains (Real.log 2) := by
    have h := factorTwoPrimeLogTwoInterval_contains
    unfold YoshidaFactorTwoPhasePerturbationMomentSeries.factorTwoMomentLength
      YoshidaEndpointHyperbolicBound.yoshidaEndpointA at h
    convert h using 1
    ring
  simpa only [factorTwoPrimeLogTwoInterval, RatInterval.Contains,
    Rat.cast_div, Rat.cast_ofNat] using hlog

private theorem log_five_four_gt_2231435_div_ten_million :
    (2231435 / 10000000 : ℝ) < Real.log (5 / 4 : ℝ) := by
  have h := Real.sum_range_le_log_div (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

private theorem fourCellScalar_eq_clean_add_log_five_four :
    Real.log (2 * (5 * Real.log 2 / 8)) +
        Real.eulerMascheroniConstant + Real.log Real.pi =
      yoshidaEndpointScalarMassLoss + Real.log (5 / 4 : ℝ) := by
  have hlogTwo : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [show 2 * (5 * Real.log 2 / 8) =
      (5 / 4 : ℝ) * Real.log 2 by ring,
    Real.log_mul (by norm_num : (5 / 4 : ℝ) ≠ 0) hlogTwo]
  unfold yoshidaEndpointScalarMassLoss
  rw [Real.log_mul Real.pi_ne_zero hlogTwo]
  ring

private theorem fourCellTotalScalar_gt_2271723_div_million :
    (2271723 / 1000000 : ℝ) <
      Real.log 2 +
        (Real.log (2 * (5 * Real.log 2 / 8)) +
          Real.eulerMascheroniConstant + Real.log Real.pi) := by
  rw [fourCellScalar_eq_clean_add_log_five_four]
  have hmass := plusP5_scalarMassLoss_fine_bounds.1
  have hlog := fine_log_two_bounds.1
  have hfive := log_five_four_gt_2231435_div_ten_million
  linarith

private theorem sqrt_two_gt_141421_div_100000 :
    (141421 / 100000 : ℝ) < Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg 2
  nlinarith

private def localCoshLower6 (u : ℝ) : ℝ :=
  1 + u ^ 2 / 2 + u ^ 4 / 24 + u ^ 6 / 720

private def localCoshUpper8 (u : ℝ) : ℝ :=
  localCoshLower6 u + (16 / 15 : ℝ) * u ^ 8 / 40320

private theorem cosh_lt_sixteen_fifteenths_local
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (1733 / 5000 : ℝ)) :
    Real.cosh u < (16 / 15 : ℝ) := by
  have huSq : u ^ 2 < (1733 / 5000 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hu hu0 (by norm_num)
  have hv0 : 0 ≤ u ^ 2 / 2 := by positivity
  have hv16 : u ^ 2 / 2 < (1 / 16 : ℝ) := by
    norm_num at huSq ⊢
    nlinarith
  have hv1 : u ^ 2 / 2 < (1 : ℝ) := hv16.trans (by norm_num)
  have hExp : Real.exp (u ^ 2 / 2) ≤ 1 / (1 - u ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hv0 hv1
  have hFrac : 1 / (1 - u ^ 2 / 2) < (16 / 15 : ℝ) := by
    rw [div_lt_iff₀ (sub_pos.mpr hv1)]
    nlinarith
  exact (Real.cosh_le_exp_half_sq u).trans_lt (hExp.trans_lt hFrac)

private theorem cosh_le_localCoshUpper8
    {u : ℝ} (hu0 : 0 ≤ u) (hu : u < (1733 / 5000 : ℝ)) :
    Real.cosh u ≤ localCoshUpper8 u := by
  rcases eq_or_lt_of_le hu0 with rfl | hupos
  · norm_num [localCoshUpper8, localCoshLower6]
  · rcases taylor_mean_remainder_lagrange_iteratedDeriv
        (f := Real.cosh) (x₀ := 0) (x := u) (n := 7) hupos
        Real.contDiff_cosh.contDiffOn with ⟨v, hv, hTaylor⟩
    have hTaylorEval :
        taylorWithinEval Real.cosh 7 (Icc 0 u) 0 u =
          localCoshLower6 u := by
      have hder (n : ℕ) :
          iteratedDerivWithin n Real.cosh (Icc 0 u) 0 =
            iteratedDeriv n Real.cosh 0 :=
        Real.iteratedDerivWithin_cosh_Icc n hupos ⟨le_rfl, hu0⟩
      rw [taylor_within_apply]
      simp [hder, Finset.sum_range_succ, localCoshLower6]
      ring
    rw [hTaylorEval] at hTaylor
    norm_num [Real.iteratedDeriv_even_cosh] at hTaylor
    have hvBound : Real.cosh v < (16 / 15 : ℝ) :=
      cosh_lt_sixteen_fifteenths_local hv.1.le (hv.2.trans hu)
    have hremUpper :
        Real.cosh v * u ^ 8 / 40320 ≤
          (16 / 15 : ℝ) * u ^ 8 / 40320 := by
      gcongr
    unfold localCoshUpper8
    linarith

private theorem fourCellEvenStripWitness_coshMoment_lt :
    fourCellPositiveCoshMoment fourCellEvenStripWitness
        (5 * Real.log 2 / 16) <
      (764291 / 500000 : ℝ) := by
  let L₁ : ℝ := 69314718055995 / 100000000000000
  let ell₁ : ℝ := 5 * L₁ / 16
  let A : ℝ := 1 + (16 / 15 : ℝ) * ell₁ ^ 8 / 40320
  let B : ℝ := ell₁ ^ 2 / 2
  let C : ℝ := ell₁ ^ 4 / 24
  let D : ℝ := ell₁ ^ 6 / 720
  let q : ℝ → ℝ := fun x ↦ A + B * x ^ 2 + C * x ^ 4 + D * x ^ 6
  let f : ℝ → ℝ := fun x ↦
    Real.cosh ((5 * Real.log 2 / 16) * x) * fourCellEvenStripWitness x
  let g : ℝ → ℝ := fun x ↦ q x * fourCellEvenStripWitness x
  have hell : 5 * Real.log 2 / 16 ≤ ell₁ := by
    dsimp only [ell₁, L₁]
    nlinarith [fine_log_two_bounds.2]
  have hf : Continuous f := by
    dsimp only [f]
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      Real.cosh ((5 * Real.log 2 / 16) * x))).mul
        fourCellEvenStripWitness_contDiff.continuous
  have hg : Continuous g := by
    exact (by
      dsimp only [q, A, B, C, D, ell₁, L₁]
      fun_prop : Continuous q).mul
        fourCellEvenStripWitness_contDiff.continuous
  have hpoint {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : f x ≤ g x := by
    let z : ℝ := (5 * Real.log 2 / 16) * x
    have hz0 : 0 ≤ z := by
      dsimp only [z]
      exact mul_nonneg (by positivity) hx.1
    have hzle : z ≤ ell₁ := by
      have hzx : z ≤ ell₁ * x := by
        dsimp only [z]
        exact mul_le_mul_of_nonneg_right hell hx.1
      have hell0 : 0 ≤ ell₁ := by norm_num [ell₁, L₁]
      exact hzx.trans (mul_le_of_le_one_right hell0 hx.2)
    have hzsmall : z < (1733 / 5000 : ℝ) := by
      exact hzle.trans_lt (by norm_num [ell₁, L₁])
    have hcosh := cosh_le_localCoshUpper8 hz0 hzsmall
    have hz2 : z ^ 2 ≤ (ell₁ * x) ^ 2 := by
      have hzx : z ≤ ell₁ * x := by
        dsimp only [z]
        exact mul_le_mul_of_nonneg_right hell hx.1
      gcongr
    have hz4 : z ^ 4 ≤ (ell₁ * x) ^ 4 := by
      have hzx : z ≤ ell₁ * x := by
        dsimp only [z]
        exact mul_le_mul_of_nonneg_right hell hx.1
      gcongr
    have hz6 : z ^ 6 ≤ (ell₁ * x) ^ 6 := by
      have hzx : z ≤ ell₁ * x := by
        dsimp only [z]
        exact mul_le_mul_of_nonneg_right hell hx.1
      gcongr
    have hz8 : z ^ 8 ≤ ell₁ ^ 8 := by gcongr
    have hcoshQ : Real.cosh z ≤ q x := by
      dsimp only [q, A, B, C, D]
      unfold localCoshUpper8 localCoshLower6 at hcosh
      rw [show (ell₁ * x) ^ 2 = ell₁ ^ 2 * x ^ 2 by ring] at hz2
      rw [show (ell₁ * x) ^ 4 = ell₁ ^ 4 * x ^ 4 by ring] at hz4
      rw [show (ell₁ * x) ^ 6 = ell₁ ^ 6 * x ^ 6 by ring] at hz6
      norm_num [ell₁, L₁] at hz2 hz4 hz6 hz8
      norm_num at hcosh ⊢
      linarith
    dsimp only [f, g]
    exact mul_le_mul_of_nonneg_right hcoshQ
      (fourCellEvenStripWitness_nonneg ⟨by linarith [hx.1], hx.2⟩)
  have hmono : (∫ x : ℝ in 0..1, f x) ≤ ∫ x : ℝ in 0..1, g x := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    exact fun x hx ↦ hpoint hx
  have hgValue : (∫ x : ℝ in 0..1, g x) =
      A * (32 / 21 : ℝ) + B * (64 / 315 : ℝ) +
        C * (32 / 495 : ℝ) + D * (256 / 9009 : ℝ) := by
    dsimp only [g, q]
    rw [show (fun x : ℝ ↦
        (A + B * x ^ 2 + C * x ^ 4 + D * x ^ 6) *
          fourCellEvenStripWitness x) =
      fun x ↦
        (3 * A) * x ^ 0 + 0 * x ^ 1 + (-7 * A + 3 * B) * x ^ 2 +
          0 * x ^ 3 + (5 * A - 7 * B + 3 * C) * x ^ 4 +
            0 * x ^ 5 + (-A + 5 * B - 7 * C + 3 * D) * x ^ 6 +
              0 * x ^ 7 + (-B + 5 * C - 7 * D) * x ^ 8 +
                0 * x ^ 9 + (-C + 5 * D) * x ^ 10 +
                  0 * x ^ 11 + (-D) * x ^ 12 + 0 * x ^ 13 by
      funext x
      unfold fourCellEvenStripWitness
      ring,
      integral_polynomial_thirteen]
    ring
  have hgUpper : (∫ x : ℝ in 0..1, g x) <
      (764291 / 500000 : ℝ) := by
    rw [hgValue]
    norm_num [A, B, C, D, ell₁, L₁]
  unfold fourCellPositiveCoshMoment
  change (∫ x : ℝ in 0..1, f x) < _
  exact hmono.trans_lt hgUpper

/-! ## A structural lower bound for the regular square -/

private theorem integral_regularPolynomial6_mul_witness_correlation :
    (∫ t : ℝ in 0..8 / 5,
      yoshidaRegularKernelPolynomial6 ((5 * Real.log 2 / 8) * t) *
        centeredEndpointCorrelation fourCellEvenStripWitness t) =
      446745206441984 / 384906005859375 -
        (8918277568256 / 353485107421875 : ℝ) * Real.log 2 -
        (17403735685376 / 1154718017578125 : ℝ) * Real.log 2 ^ 2 +
        (2603730415976 / 18027740478515625 : ℝ) * Real.log 2 ^ 3 +
        (302541666032 / 692830810546875 : ℝ) * Real.log 2 ^ 4 -
        (22399446708178 / 16783826385498046875 : ℝ) * Real.log 2 ^ 5 -
        (4780828567898 / 259811553955078125 : ℝ) * Real.log 2 ^ 6 := by
  let L : ℝ := Real.log 2
  change (∫ t : ℝ in 0..8 / 5,
      yoshidaRegularKernelPolynomial6 ((5 * L / 8) * t) *
        centeredEndpointCorrelation fourCellEvenStripWitness t) = _
  rw [show (fun t : ℝ ↦
      yoshidaRegularKernelPolynomial6 ((5 * L / 8) * t) *
        centeredEndpointCorrelation fourCellEvenStripWitness t) =
      fun t ↦
        (25856 / 15015) * t ^ 0 +
        (-808 * L / 9009) * t ^ 1 +
        (-5 * (101 * L ^ 2 + 3328) / 6006) * t ^ 2 +
        (5 * L * (707 * L ^ 2 + 99840) / 3459456) * t ^ 3 +
        ((63125 * L ^ 4 + 2496000 * L ^ 2 + 42172416) /
          18450432) * t ^ 4 +
        (-(1956875 * L ^ 5 + 305760000 * L ^ 3 +
          22140518400 * L + 99189522432) / 185980354560) * t ^ 5 +
        (-(3850625 * L ^ 6 + 156000000 * L ^ 4 +
          3162931200 * L ^ 2 - 787218432 * L + 21592276992) /
            28339863552) * t ^ 6 +
        ((96875 * L ^ 5 + 7761600 * L ^ 3 + 149022720 * L ^ 2 +
          227082240 * L + 2179989504) / 5722472448) * t ^ 7 +
        (5 * L * (190625 * L ^ 5 + 3960000 * L ^ 3 -
          275968 * L ^ 2 + 32440320 * L - 17301504) /
            4359979008) * t ^ 8 +
        (-(19375 * L ^ 5 + 1470000 * L ^ 4 + 627200 * L ^ 3 +
          25804800 * L ^ 2 + 33030144) / 1387266048) * t ^ 9 +
        (-5 * L * (343125 * L ^ 5 - 6200 * L ^ 4 +
          2880000 * L ^ 3 - 430080 * L ^ 2 - 2359296) /
            9512681472) * t ^ 10 +
        ((61648125 * L ^ 6 + 6820000 * L ^ 5 + 1108800000 * L ^ 4 +
          1703116800 * L ^ 2 + 1585446912) / 1464952946688) * t ^ 11 +
        (5 * L * (8806875 * L ^ 5 - 341000 * L ^ 4 -
          2069760 * L ^ 2 - 8257536) / 732476473344) * t ^ 12 +
        (-(27259375 * L ^ 6 + 42900000 * L ^ 4 +
          47923200 * L ^ 2 + 18874368) / 906875633664) * t ^ 13 +
        (5 * L * (554125 * L ^ 4 + 2446080 * L ^ 2 + 4128768) /
          19044388306944) * t ^ 14 +
        (25 * L ^ 2 * (1090375 * L ^ 4 + 1248000 * L ^ 2 + 589824) /
          14510010138624) * t ^ 15 +
        (-25 * L ^ 3 * (10075 * L ^ 2 + 18816) /
          38088776613888) * t ^ 16 +
        (-3125 * L ^ 4 * (793 * L ^ 2 + 384) /
          29020020277248) * t ^ 17 +
        (19375 * L ^ 5 / 152355106455552) * t ^ 18 +
        (190625 * L ^ 6 / 116080081108992) * t ^ 19 by
      funext t
      rw [centeredEndpointCorrelation_fourCellEvenStripWitness]
      unfold yoshidaRegularKernelPolynomial6
      ring,
    integral_polynomial_nineteen]
  dsimp only [L]
  ring

private theorem integral_regularPolynomial6_mul_witness_correlation_gt :
    (113607 / 100000 : ℝ) <
      ∫ t : ℝ in 0..8 / 5,
        yoshidaRegularKernelPolynomial6 ((5 * Real.log 2 / 8) * t) *
          centeredEndpointCorrelation fourCellEvenStripWitness t := by
  let L₀ : ℝ := 69314718055994 / 100000000000000
  let L₁ : ℝ := 69314718055995 / 100000000000000
  have hL := fine_log_two_bounds
  have hL₀ : 0 ≤ L₀ := by norm_num [L₀]
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hL₁ : 0 ≤ L₁ := by norm_num [L₁]
  have hL₀log : L₀ ≤ Real.log 2 := by simpa only [L₀] using hL.1
  have hlo3 : L₀ ^ 3 ≤ Real.log 2 ^ 3 := by gcongr
  have hlo4 : L₀ ^ 4 ≤ Real.log 2 ^ 4 := by gcongr
  have hup1 : Real.log 2 ≤ L₁ := hL.2
  have hup2 : Real.log 2 ^ 2 ≤ L₁ ^ 2 := by gcongr
  have hup5 : Real.log 2 ^ 5 ≤ L₁ ^ 5 := by gcongr
  have hup6 : Real.log 2 ^ 6 ≤ L₁ ^ 6 := by gcongr
  rw [integral_regularPolynomial6_mul_witness_correlation]
  have hrat :
      (113607 / 100000 : ℝ) <
        446745206441984 / 384906005859375 -
          (8918277568256 / 353485107421875 : ℝ) * L₁ -
          (17403735685376 / 1154718017578125 : ℝ) * L₁ ^ 2 +
          (2603730415976 / 18027740478515625 : ℝ) * L₀ ^ 3 +
          (302541666032 / 692830810546875 : ℝ) * L₀ ^ 4 -
          (22399446708178 / 16783826385498046875 : ℝ) * L₁ ^ 5 -
          (4780828567898 / 259811553955078125 : ℝ) * L₁ ^ 6 := by
    norm_num [L₀, L₁]
  apply hrat.trans_le
  gcongr

private theorem centeredEndpointCorrelation_fourCellEvenStripWitness_nonneg
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    0 ≤ centeredEndpointCorrelation fourCellEvenStripWitness t := by
  unfold centeredEndpointCorrelation
  apply intervalIntegral.integral_nonneg (by linarith [ht.2])
  intro x hx
  have hxI : x ∈ Icc (-1 : ℝ) (1 - t) := by
    simpa only [uIcc_of_le (by linarith [ht.2] : (-1 : ℝ) ≤ 1 - t)] using hx
  have htxI : t + x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [ht.1, hxI.1, hxI.2]
  have hxUnit : x ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [ht.1, hxI.1, hxI.2]
  exact mul_nonneg (fourCellEvenStripWitness_nonneg htxI)
    (fourCellEvenStripWitness_nonneg hxUnit)

private theorem continuous_centeredEndpointCorrelation_fourCellEvenStripWitness :
    Continuous (centeredEndpointCorrelation fourCellEvenStripWitness) := by
  rw [show centeredEndpointCorrelation fourCellEvenStripWitness =
      fun t : ℝ ↦
        103424 / 15015 - (2560 / 231 : ℝ) * t ^ 2 +
          (64 / 7 : ℝ) * t ^ 4 - (32 / 15 : ℝ) * t ^ 5 -
            (64 / 21 : ℝ) * t ^ 6 + (32 / 21 : ℝ) * t ^ 7 -
              (2 / 21 : ℝ) * t ^ 9 + (1 / 231 : ℝ) * t ^ 11 -
                (1 / 12012 : ℝ) * t ^ 13 by
    funext t
    exact centeredEndpointCorrelation_fourCellEvenStripWitness t]
  fun_prop

private theorem intervalIntegrable_regularKernel_mul_witnessCorrelation :
    IntervalIntegrable
      (fun t : ℝ ↦
        yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
          centeredEndpointCorrelation fourCellEvenStripWitness t)
      volume 0 2 := by
  let C : ℝ → ℝ := fun t ↦
    centeredEndpointCorrelation fourCellEvenStripWitness t
  let f : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) * C t
  let g : ℝ → ℝ := fun t ↦ (1 / 4 : ℝ) * |C t|
  have hC : Continuous C :=
    continuous_centeredEndpointCorrelation_fourCellEvenStripWitness
  have hgIcc : IntegrableOn g (Icc (0 : ℝ) 2) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_const.mul hC.abs).continuousOn
  have hg : Integrable g (volume.restrict (Ioc (0 : ℝ) 2)) :=
    hgIcc.mono_set Ioc_subset_Icc_self
  have hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 2)) := by
    apply Measurable.aestronglyMeasurable
    dsimp only [f]
    exact (measurable_yoshidaRegularKernel.comp
      (measurable_const.mul measurable_id)).mul hC.measurable
  have hfg : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 2)),
      ‖f t‖ ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have harg0 : 0 ≤ (5 * Real.log 2 / 8) * t :=
      mul_nonneg (by positivity) ht.1.le
    have harg : (5 * Real.log 2 / 8) * t ≤ 5 * Real.log 2 / 4 := by
      have ha : 0 ≤ 5 * Real.log 2 / 8 := by positivity
      have hmul := mul_le_mul_of_nonneg_left ht.2 ha
      linarith
    have hk0 := yoshidaRegularKernel_nonneg_fourCellRange harg0 harg
    have hk1 := yoshidaRegularKernel_le_quarter harg0
    dsimp only [f, g]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
    exact mul_le_mul_of_nonneg_right hk1 (abs_nonneg (C t))
  constructor
  · exact Integrable.mono' hg hfmeas hfg
  · simp

private theorem regularMoment_fourCellEvenStripWitness_gt :
    (113607 / 100000 : ℝ) <
      ∫ t : ℝ in 0..2,
        yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
          centeredEndpointCorrelation fourCellEvenStripWitness t := by
  let C : ℝ → ℝ := fun t ↦
    centeredEndpointCorrelation fourCellEvenStripWitness t
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernel ((5 * Real.log 2 / 8) * t)
  let P : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 ((5 * Real.log 2 / 8) * t)
  have hC : Continuous C :=
    continuous_centeredEndpointCorrelation_fourCellEvenStripWitness
  have hP : Continuous P := by
    dsimp only [P]
    unfold yoshidaRegularKernelPolynomial6
    fun_prop
  have hfull : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 2 := by
    simpa only [K, C] using
      intervalIntegrable_regularKernel_mul_witnessCorrelation
  have hleft : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume 0 (8 / 5) :=
    hfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (0 : ℝ) (8 / 5) ⊆ uIcc (0 : ℝ) 2)
  have htail : IntervalIntegrable (fun t : ℝ ↦ K t * C t)
      volume (8 / 5) 2 :=
    hfull.mono_set (by
      intro t ht
      norm_num at ht ⊢
      constructor <;> linarith :
        uIcc (8 / 5 : ℝ) 2 ⊆ uIcc (0 : ℝ) 2)
  have hpoly : IntervalIntegrable (fun t : ℝ ↦ P t * C t)
      volume 0 (8 / 5) := (hP.mul hC).intervalIntegrable _ _
  have hleftMono :
      (∫ t : ℝ in 0..8 / 5, P t * C t) ≤
        ∫ t : ℝ in 0..8 / 5, K t * C t := by
    apply intervalIntegral.integral_mono_on (by norm_num) hpoly hleft
    intro t ht
    have harg0 : 0 ≤ (5 * Real.log 2 / 8) * t :=
      mul_nonneg (by positivity) ht.1
    have hargLog : (5 * Real.log 2 / 8) * t ≤ Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by positivity : 0 ≤ 5 * Real.log 2 / 8)
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    have henv := yoshidaRegularKernelPolynomial6_envelope harg0 hargLog
    have hC0 : 0 ≤ C t := by
      exact centeredEndpointCorrelation_fourCellEvenStripWitness_nonneg
        ⟨ht.1, by linarith [ht.2]⟩
    dsimp only [K, P]
    nlinarith [mul_nonneg henv.1 hC0]
  have htailNonneg :
      0 ≤ ∫ t : ℝ in 8 / 5..2, K t * C t := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro t ht
    have harg0 : 0 ≤ (5 * Real.log 2 / 8) * t :=
      mul_nonneg (by positivity) (by linarith [ht.1])
    have harg : (5 * Real.log 2 / 8) * t ≤ 5 * Real.log 2 / 4 := by
      have hmul := mul_le_mul_of_nonneg_left ht.2
        (by positivity : 0 ≤ 5 * Real.log 2 / 8)
      linarith
    exact mul_nonneg (yoshidaRegularKernel_nonneg_fourCellRange harg0 harg)
      (centeredEndpointCorrelation_fourCellEvenStripWitness_nonneg
        ⟨by linarith [ht.1], ht.2⟩)
  have hmodel : (113607 / 100000 : ℝ) <
      ∫ t : ℝ in 0..8 / 5, P t * C t := by
    simpa only [P, C] using
      integral_regularPolynomial6_mul_witness_correlation_gt
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft htail
  calc
    (113607 / 100000 : ℝ) <
        ∫ t : ℝ in 0..8 / 5, P t * C t := hmodel
    _ ≤ ∫ t : ℝ in 0..8 / 5, K t * C t := hleftMono
    _ ≤ (∫ t : ℝ in 0..8 / 5, K t * C t) +
        ∫ t : ℝ in 8 / 5..2, K t * C t := by linarith
    _ = ∫ t : ℝ in 0..2, K t * C t := hsplit
    _ = ∫ t : ℝ in 0..2,
        yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
          centeredEndpointCorrelation fourCellEvenStripWitness t := rfl

private theorem fourCellEvenStripWitness_coshMoment_nonneg :
    0 ≤ fourCellPositiveCoshMoment fourCellEvenStripWitness
      (5 * Real.log 2 / 16) := by
  unfold fourCellPositiveCoshMoment
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro x hx
  exact mul_nonneg (Real.cosh_pos _).le
    (fourCellEvenStripWitness_nonneg ⟨by linarith [hx.1], hx.2⟩)

private theorem fourCellEvenStripWitness_polarRank_lt :
    8 * (5 * Real.log 2 / 8) *
        fourCellPositiveCoshMoment fourCellEvenStripWitness
          (5 * Real.log 2 / 16) ^ 2 <
      (809792 / 100000 : ℝ) := by
  let L₁ : ℝ := 69314718055995 / 100000000000000
  let H : ℝ := fourCellPositiveCoshMoment fourCellEvenStripWitness
    (5 * Real.log 2 / 16)
  let U : ℝ := 764291 / 500000
  have hH0 : 0 ≤ H := fourCellEvenStripWitness_coshMoment_nonneg
  have hHU : H < U := fourCellEvenStripWitness_coshMoment_lt
  have hHSq : H ^ 2 < U ^ 2 := by
    nlinarith [mul_self_lt_mul_self hH0 hHU]
  have ha0 : 0 < 5 * Real.log 2 / 8 := by positivity
  have haUpper : 5 * Real.log 2 / 8 ≤ 5 * L₁ / 8 := by
    dsimp only [L₁]
    nlinarith [fine_log_two_bounds.2]
  change 8 * (5 * Real.log 2 / 8) * H ^ 2 < _
  calc
    8 * (5 * Real.log 2 / 8) * H ^ 2 <
        8 * (5 * Real.log 2 / 8) * U ^ 2 :=
      mul_lt_mul_of_pos_left hHSq (by positivity)
    _ ≤ 8 * (5 * L₁ / 8) * U ^ 2 := by gcongr
    _ < (809792 / 100000 : ℝ) := by
      norm_num [L₁, U]

theorem fourCellBracket_fourCellEvenStripWitness_eq :
    centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8)
          fourCellEvenStripWitness -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing fourCellEvenStripWitness =
      5786089216 / 676350675 -
        Real.sqrt 2 * Real.log 2 *
          (72358908928 / 3665771484375) -
        2 * (51712 / 15015 : ℝ) *
          (Real.log 2 +
            (Real.log (2 * (5 * Real.log 2 / 8)) +
              Real.eulerMascheroniConstant + Real.log Real.pi)) -
        2 * (5 * Real.log 2 / 8) *
          (∫ t : ℝ in 0..2,
            yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
              centeredEndpointCorrelation fourCellEvenStripWitness t) +
        8 * (5 * Real.log 2 / 8) *
          fourCellPositiveCoshMoment fourCellEvenStripWitness
            (5 * Real.log 2 / 16) ^ 2 := by
  have hpolar := physicalPolarProduct_eq_positiveCoshSquare_of_even
    fourCellEvenStripWitness fourCellEvenStripWitness_contDiff.continuous
      fourCellEvenStripWitness_even (5 * Real.log 2 / 8)
  unfold centeredClippedPhysicalQuadratic
  rw [centeredRawLogEnergy_fourCellEvenStripWitness,
    endpointPotential_fourCellEvenStripWitness_eq,
    integral_full_fourCellEvenStripWitness_sq,
    fourCellEndpointPairing_fourCellEvenStripWitness, hpolar]
  ring

/-- The complete bracket on the witness is positive but smaller than the
exact strip-gap slack discarded by the capacity reduction. -/
private theorem fourCellBracket_fourCellEvenStripWitness_lt :
    centeredClippedPhysicalQuadratic (5 * Real.log 2 / 8)
          fourCellEvenStripWitness -
        Real.sqrt 2 * Real.log 2 *
          fourCellEndpointPairing fourCellEvenStripWitness <
      (19 / 10000 : ℝ) := by
  let L₀ : ℝ := 69314718055994 / 100000000000000
  let beta₀ : ℝ := (141421 / 100000 : ℝ) * L₀
  let p : ℝ := 72358908928 / 3665771484375
  let M : ℝ := 51712 / 15015
  let T₀ : ℝ := 2271723 / 1000000
  let R₀ : ℝ := 113607 / 100000
  let a₀ : ℝ := 5 * L₀ / 8
  let I : ℝ := ∫ t : ℝ in 0..2,
    yoshidaRegularKernel ((5 * Real.log 2 / 8) * t) *
      centeredEndpointCorrelation fourCellEvenStripWitness t
  let T : ℝ := Real.log 2 +
    (Real.log (2 * (5 * Real.log 2 / 8)) +
      Real.eulerMascheroniConstant + Real.log Real.pi)
  have hbeta : beta₀ < Real.sqrt 2 * Real.log 2 := by
    calc
      beta₀ ≤ (141421 / 100000 : ℝ) * Real.log 2 := by
        dsimp only [beta₀, L₀]
        gcongr
        exact fine_log_two_bounds.1
      _ < Real.sqrt 2 * Real.log 2 := by
        exact mul_lt_mul_of_pos_right sqrt_two_gt_141421_div_100000
          (Real.log_pos (by norm_num))
  have hbetaTerm : beta₀ * p <
      (Real.sqrt 2 * Real.log 2) * p := by
    exact mul_lt_mul_of_pos_right hbeta (by norm_num [p])
  have hscalar : T₀ < T := fourCellTotalScalar_gt_2271723_div_million
  have hscalarTerm : 2 * M * T₀ < 2 * M * T := by
    exact mul_lt_mul_of_pos_left hscalar (by norm_num [M])
  have hreg : R₀ < I := regularMoment_fourCellEvenStripWitness_gt
  have ha : a₀ ≤ 5 * Real.log 2 / 8 := by
    dsimp only [a₀, L₀]
    nlinarith [fine_log_two_bounds.1]
  have hregularTerm : 2 * a₀ * R₀ <
      2 * (5 * Real.log 2 / 8) * I := by
    calc
      2 * a₀ * R₀ ≤ 2 * (5 * Real.log 2 / 8) * R₀ := by
        gcongr
      _ < 2 * (5 * Real.log 2 / 8) * I := by
        exact mul_lt_mul_of_pos_left hreg (by positivity)
  have hpolar := fourCellEvenStripWitness_polarRank_lt
  have hrat :
      5786089216 / 676350675 - beta₀ * p -
          2 * M * T₀ - 2 * a₀ * R₀ +
            (809792 / 100000 : ℝ) < 19 / 10000 := by
    norm_num [beta₀, p, M, T₀, R₀, a₀, L₀]
  rw [fourCellBracket_fourCellEvenStripWitness_eq]
  let R : ℝ := 5786089216 / 676350675
  let B₀ : ℝ := beta₀ * p
  let B : ℝ := (Real.sqrt 2 * Real.log 2) * p
  let S₀ : ℝ := 2 * M * T₀
  let S : ℝ := 2 * M * T
  let Q₀ : ℝ := 2 * a₀ * R₀
  let Q : ℝ := 2 * (5 * Real.log 2 / 8) * I
  let P : ℝ := 8 * (5 * Real.log 2 / 8) *
    fourCellPositiveCoshMoment fourCellEvenStripWitness
      (5 * Real.log 2 / 16) ^ 2
  let U : ℝ := 809792 / 100000
  change B₀ < B at hbetaTerm
  change S₀ < S at hscalarTerm
  change Q₀ < Q at hregularTerm
  change P < U at hpolar
  change R - B₀ - S₀ - Q₀ + U < 19 / 10000 at hrat
  change R - B - S - Q + P < 19 / 10000
  calc
    R - B - S - Q + P < R - B₀ - S - Q + P := by linarith
    _ < R - B₀ - S₀ - Q + P := by linarith
    _ < R - B₀ - S₀ - Q₀ + P := by linarith
    _ < R - B₀ - S₀ - Q₀ + U := by linarith
    _ < 19 / 10000 := hrat

/-! ## Exact strip-gap slack on the witness -/

private def fourCellEvenStripWitnessStripEven (z : ℝ) : ℝ :=
  -z ^ 6 / 15625 - 23 * z ^ 4 / 3125 +
    757 * z ^ 2 / 3125 + 4779 / 15625

private theorem fourCellOddEndpointStripEven_witness_eq (z : ℝ) :
    fourCellOddEndpointStripEven fourCellEvenStripWitness z =
      fourCellEvenStripWitnessStripEven z := by
  unfold fourCellOddEndpointStripEven fourCellOddEndpointStripPullback
    fourCellEvenStripWitness fourCellEvenStripWitnessStripEven
  ring

private theorem fourCellEvenEndpointStripMean_witness_eq :
    fourCellEvenEndpointStripMean fourCellEvenStripWitness =
      126368 / 328125 := by
  unfold fourCellEvenEndpointStripMean centeredIntervalMean
  rw [show fourCellOddEndpointStripEven fourCellEvenStripWitness =
      fourCellEvenStripWitnessStripEven by
    funext z
    exact fourCellOddEndpointStripEven_witness_eq z]
  rw [show fourCellEvenStripWitnessStripEven = fun z : ℝ ↦
      (4779 / 15625) * z ^ 0 + 0 * z ^ 1 +
        (757 / 3125) * z ^ 2 + 0 * z ^ 3 +
          (-23 / 3125) * z ^ 4 + 0 * z ^ 5 +
            (-1 / 15625) * z ^ 6 + 0 * z ^ 7 + 0 * z ^ 8 +
              0 * z ^ 9 + 0 * z ^ 10 + 0 * z ^ 11 +
                0 * z ^ 12 + 0 * z ^ 13 by
    funext z
    unfold fourCellEvenStripWitnessStripEven
    ring,
    integral_polynomial_thirteen]
  norm_num

private def fourCellEvenStripWitnessStripResidual (z : ℝ) : ℝ :=
  -z ^ 6 / 15625 - 23 * z ^ 4 / 3125 +
    757 * z ^ 2 / 3125 - 26009 / 328125

private theorem fourCellEvenEndpointStripResidual_witness_eq (z : ℝ) :
    fourCellEvenEndpointStripResidual fourCellEvenStripWitness z =
      fourCellEvenStripWitnessStripResidual z := by
  unfold fourCellEvenEndpointStripResidual
  rw [fourCellOddEndpointStripEven_witness_eq,
    fourCellEvenEndpointStripMean_witness_eq]
  unfold fourCellEvenStripWitnessStripEven
    fourCellEvenStripWitnessStripResidual
  ring

private theorem fourCellEvenEndpointStripResidualMass_witness_eq :
    fourCellEvenEndpointStripResidualMass fourCellEvenStripWitness =
      152308345856 / 76981201171875 := by
  unfold fourCellEvenEndpointStripResidualMass
  rw [show fourCellEvenEndpointStripResidual fourCellEvenStripWitness =
      fourCellEvenStripWitnessStripResidual by
    funext z
    exact fourCellEvenEndpointStripResidual_witness_eq z]
  rw [show (fun z : ℝ ↦ fourCellEvenStripWitnessStripResidual z ^ 2) =
      fun z ↦
        (676468081 / 107666015625) * z ^ 0 + 0 * z ^ 1 +
          (-39377626 / 1025390625) * z ^ 2 + 0 * z ^ 3 +
            (61366559 / 1025390625) * z ^ 4 + 0 * z ^ 5 +
              (-18229532 / 5126953125) * z ^ 6 + 0 * z ^ 7 +
                (1131 / 48828125) * z ^ 8 + 0 * z ^ 9 +
                  (46 / 48828125) * z ^ 10 + 0 * z ^ 11 +
                    (1 / 244140625) * z ^ 12 + 0 * z ^ 13 by
    funext z
    unfold fourCellEvenStripWitnessStripResidual
    ring,
    integral_polynomial_thirteen]
  norm_num

private theorem centeredPositiveDistanceEnergy_witnessStripEven (t : ℝ) :
    centeredPositiveDistanceEnergy fourCellEvenStripWitnessStripEven t =
      t * (-(71 / 112792968750 : ℝ) * t ^ 12 +
        (2 / 244140625 : ℝ) * t ^ 11 -
          (1126 / 5126953125 : ℝ) * t ^ 10 +
            (504 / 244140625 : ℝ) * t ^ 9 -
              (15476 / 1025390625 : ℝ) * t ^ 8 +
                (18408 / 244140625 : ℝ) * t ^ 7 +
                  (518528 / 732421875 : ℝ) * t ^ 6 -
                    (6766208 / 1025390625 : ℝ) * t ^ 5 +
                      (148672 / 146484375 : ℝ) * t ^ 4 +
                        (29026688 / 341796875 : ℝ) * t ^ 3 -
                          (50466816 / 244140625 : ℝ) * t ^ 2 +
                            (8189699072 / 56396484375 : ℝ) * t) := by
  unfold centeredPositiveDistanceEnergy
  rw [show (fun x : ℝ ↦
      (fourCellEvenStripWitnessStripEven (t + x) -
        fourCellEvenStripWitnessStripEven x) ^ 2) =
      fun x ↦
        (t ^ 4 * (t ^ 4 + 115 * t ^ 2 - 3785) ^ 2 / 244140625) * x ^ 0 +
        (4 * t ^ 3 * (t ^ 4 + 115 * t ^ 2 - 3785) *
          (3 * t ^ 4 + 230 * t ^ 2 - 3785) / 244140625) * x ^ 1 +
        (2 * t ^ 2 * (33 * t ^ 8 + 5175 * t ^ 6 + 82955 * t ^ 4 -
          6093850 * t ^ 2 + 28652450) / 244140625) * x ^ 2 +
        (4 * t ^ 3 * (11 * t ^ 6 + 1380 * t ^ 4 + 18105 * t ^ 2 -
          696440) / 48828125) * x ^ 3 +
        (t ^ 2 * (99 * t ^ 6 + 9614 * t ^ 4 + 96590 * t ^ 2 -
          1392880) / 48828125) * x ^ 4 +
        (12 * t ^ 3 * (66 * t ^ 4 + 4715 * t ^ 2 + 30190) /
          244140625) * x ^ 5 +
        (2 * t ^ 2 * (461 * t ^ 4 + 22310 * t ^ 2 + 60380) /
          244140625) * x ^ 6 +
        (12 * t ^ 3 * (13 * t ^ 2 + 368) / 48828125) * x ^ 7 +
        (3 * t ^ 2 * (31 * t ^ 2 + 368) / 48828125) * x ^ 8 +
        (36 * t ^ 3 / 48828125) * x ^ 9 +
        (36 * t ^ 2 / 244140625) * x ^ 10 +
          0 * x ^ 11 + 0 * x ^ 12 + 0 * x ^ 13 by
    funext x
    unfold fourCellEvenStripWitnessStripEven
    ring,
    integral_polynomial_thirteen]
  ring

private theorem centeredRawLogEnergy_witnessStripEven_eq :
    centeredRawLogEnergy fourCellEvenStripWitnessStripEven =
      1958299730432 / 32991943359375 := by
  let Q : ℝ → ℝ := fun t ↦
    -(71 / 112792968750 : ℝ) * t ^ 12 +
      (2 / 244140625 : ℝ) * t ^ 11 -
        (1126 / 5126953125 : ℝ) * t ^ 10 +
          (504 / 244140625 : ℝ) * t ^ 9 -
            (15476 / 1025390625 : ℝ) * t ^ 8 +
              (18408 / 244140625 : ℝ) * t ^ 7 +
                (518528 / 732421875 : ℝ) * t ^ 6 -
                  (6766208 / 1025390625 : ℝ) * t ^ 5 +
                    (148672 / 146484375 : ℝ) * t ^ 4 +
                      (29026688 / 341796875 : ℝ) * t ^ 3 -
                        (50466816 / 244140625 : ℝ) * t ^ 2 +
                          (8189699072 / 56396484375 : ℝ) * t
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1)
      fourCellEvenStripWitnessStripEven := by
    have hdiff : ContDiff ℝ 1 fourCellEvenStripWitnessStripEven := by
      unfold fourCellEvenStripWitnessStripEven
      fun_prop
    exact hdiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hfold :=
    half_integral_positiveDistanceEnergy_eq_centeredRaw_of_locallyLipschitzOn
      fourCellEvenStripWitnessStripEven hlocal
  have hpoint (t : ℝ) :
      centeredPositiveDistanceEnergy fourCellEvenStripWitnessStripEven t / t =
        Q t := by
    rw [centeredPositiveDistanceEnergy_witnessStripEven]
    dsimp only [Q]
    by_cases ht : t = 0
    · simp [ht]
    · field_simp [ht]
  have hQ : (∫ t : ℝ in 0..2, Q t) =
      979149865216 / 32991943359375 := by
    rw [show Q = fun t : ℝ ↦
        0 * t ^ 0 + (8189699072 / 56396484375) * t ^ 1 +
          (-50466816 / 244140625) * t ^ 2 +
            (29026688 / 341796875) * t ^ 3 +
              (148672 / 146484375) * t ^ 4 +
                (-6766208 / 1025390625) * t ^ 5 +
                  (518528 / 732421875) * t ^ 6 +
                    (18408 / 244140625) * t ^ 7 +
                      (-15476 / 1025390625) * t ^ 8 +
                        (504 / 244140625) * t ^ 9 +
                          (-1126 / 5126953125) * t ^ 10 +
                            (2 / 244140625) * t ^ 11 +
                              (-71 / 112792968750) * t ^ 12 +
                                0 * t ^ 13 by
      funext t
      dsimp only [Q]
      ring,
      integral_polynomial_thirteen]
    norm_num
  rw [show (fun t : ℝ ↦
      centeredPositiveDistanceEnergy fourCellEvenStripWitnessStripEven t / t) =
      Q by
    funext t
    exact hpoint t, hQ] at hfold
  linarith

private theorem fourCellOddEndpointStripEvenRawEnergy_witness_eq :
    fourCellOddEndpointStripEvenRawEnergy fourCellEvenStripWitness =
      1958299730432 / 164959716796875 := by
  unfold fourCellOddEndpointStripEvenRawEnergy
  rw [show fourCellOddEndpointStripEven fourCellEvenStripWitness =
      fourCellEvenStripWitnessStripEven by
    funext z
    exact fourCellOddEndpointStripEven_witness_eq z,
    centeredRawLogEnergy_witnessStripEven_eq]
  ring

private theorem fourCellEvenStripWitness_gapSlack_eq :
    (1 / 2 : ℝ) *
        fourCellOddEndpointStripEvenRawEnergy fourCellEvenStripWitness -
      2 * fourCellEvenEndpointStripResidualMass fourCellEvenStripWitness =
        2284798680832 / 1154718017578125 := by
  rw [fourCellOddEndpointStripEvenRawEnergy_witness_eq,
    fourCellEvenEndpointStripResidualMass_witness_eq]
  norm_num

private theorem fourCellEvenStripWitness_gapSlack_gt :
    (19 / 10000 : ℝ) <
      (1 / 2 : ℝ) *
          fourCellOddEndpointStripEvenRawEnergy fourCellEvenStripWitness -
        2 * fourCellEvenEndpointStripResidualMass fourCellEvenStripWitness := by
  rw [fourCellEvenStripWitness_gapSlack_eq]
  norm_num

/-- Universal nonnegativity of the strip-capacity lower operator is false:
the exact smooth even endpoint-zero sextic makes it strictly negative. -/
theorem fourCellEvenStripCapacityLowerOperator_fourCellEvenStripWitness_neg :
    fourCellEvenStripCapacityLowerOperator fourCellEvenStripWitness < 0 := by
  rw [fourCellEvenStripCapacityLowerOperator_eq_completed_sub_gapSlack
    fourCellEvenStripWitness fourCellEvenStripWitness_contDiff]
  rw [← fourCellBracket_eq_evenCompletedParityOperator
    fourCellEvenStripWitness fourCellEvenStripWitness_contDiff.continuous
      (fourCellEvenStripWitness_contDiff.contDiffOn.locallyLipschitzOn
        (convex_Icc (-1) 1)) fourCellEvenStripWitness_even]
  unfold fourCellOperatorHalfWidth
  linarith [fourCellBracket_fourCellEvenStripWitness_lt,
    fourCellEvenStripWitness_gapSlack_gt]

theorem not_forall_even_contDiff_fourCellEvenStripCapacityLowerOperator_nonneg :
    ¬ ∀ w : ℝ → ℝ, ContDiff ℝ 1 w → Function.Even w →
      0 ≤ fourCellEvenStripCapacityLowerOperator w := by
  intro h
  have hw := h fourCellEvenStripWitness fourCellEvenStripWitness_contDiff
    fourCellEvenStripWitness_even
  linarith [fourCellEvenStripCapacityLowerOperator_fourCellEvenStripWitness_neg]

theorem
    not_forall_endpointZero_even_contDiff_fourCellEvenStripCapacityLowerOperator_nonneg :
    ¬ ∀ w : ℝ → ℝ, ContDiff ℝ 1 w → Function.Even w →
      w (-1) = 0 → w 1 = 0 →
        0 ≤ fourCellEvenStripCapacityLowerOperator w := by
  intro h
  have hw := h fourCellEvenStripWitness fourCellEvenStripWitness_contDiff
    fourCellEvenStripWitness_even fourCellEvenStripWitness_neg_one
      fourCellEvenStripWitness_one
  linarith [fourCellEvenStripCapacityLowerOperator_fourCellEvenStripWitness_neg]

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenStripCapacityClosureStructural
