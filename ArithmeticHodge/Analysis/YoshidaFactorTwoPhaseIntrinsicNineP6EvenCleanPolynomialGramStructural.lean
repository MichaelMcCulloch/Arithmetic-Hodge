import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenEndpointLowerModelStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanPolynomialGramStructural

noncomputable section

open CenteredEndpointCorrelation
open ShiftedLegendreBasis
open ShiftedLegendreLogEigen
open ShiftedLegendreLogKernel
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointEvenP2LogEnergy
open YoshidaEndpointEvenProjectedRemainderEnvelopeKernel
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddOneThreeRawPolarization
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialExactLowMode
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenEndpointLowerModelStructural
open YoshidaFactorTwoPhaseIntrinsicNineP6EvenProfileCorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicOddLowEndpointStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicOddP5CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanCrossStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CleanDiagonalStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4CorrelationStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4WeightedMass
open YoshidaFactorTwoPhaseIntrinsicSixProjectiveRawFourC2Structural
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur

/-!
# Exact clean polynomial Gram on `P0/P2/P4/P6`

This file evaluates the non-hyperbolic part of the degree-six clean endpoint
model on the genuine four-mode even profile.  Every entry comes from an exact
Legendre identity or exact polynomial integration.  In particular, there is
no sampling, subdivision, or numerical quadrature in the construction.
-/

/-! ## The exact regular-kernel row -/

/-- Twice the degree-six regular-kernel correlation integral in the `P0-P0`
entry. -/
def factorTwoP6EvenRegularGram00 : ℝ :=
  1 - yoshidaEndpointA / 18 - yoshidaEndpointA ^ 2 / 12 +
    7 * yoshidaEndpointA ^ 3 / 3600 + yoshidaEndpointA ^ 4 / 72 -
    31 * yoshidaEndpointA ^ 5 / 317520 -
    61 * yoshidaEndpointA ^ 6 / 20160

/-- Twice the degree-six regular-kernel correlation integral in the `P0-P2`
entry. -/
def factorTwoP6EvenRegularGram02 : ℝ :=
  -yoshidaEndpointA / 180 - yoshidaEndpointA ^ 2 / 60 +
    yoshidaEndpointA ^ 3 / 1800 + 5 * yoshidaEndpointA ^ 4 / 1008 -
    31 * yoshidaEndpointA ^ 5 / 762048 -
    61 * yoshidaEndpointA ^ 6 / 43200

/-- Twice the degree-six regular-kernel correlation integral in the `P0-P4`
entry. -/
def factorTwoP6EvenRegularGram04 : ℝ :=
  yoshidaEndpointA ^ 3 / 64800 + yoshidaEndpointA ^ 4 / 3024 -
    31 * yoshidaEndpointA ^ 5 / 6985440 -
    61 * yoshidaEndpointA ^ 6 / 285120

/-- Twice the degree-six regular-kernel correlation integral in the `P0-P6`
entry. -/
def factorTwoP6EvenRegularGram06 : ℝ :=
  -31 * yoshidaEndpointA ^ 5 / 544864320 -
    61 * yoshidaEndpointA ^ 6 / 8648640

/-- Twice the degree-six regular-kernel correlation integral in the `P2-P2`
entry. -/
def factorTwoP6EvenRegularGram22 : ℝ :=
  yoshidaEndpointA / 630 + yoshidaEndpointA ^ 3 / 10800 +
    yoshidaEndpointA ^ 4 / 720 -
    31 * yoshidaEndpointA ^ 5 / 2095632 -
    61 * yoshidaEndpointA ^ 6 / 100800

/-- Twice the degree-six regular-kernel correlation integral in the `P2-P4`
entry. -/
def factorTwoP6EvenRegularGram24 : ℝ :=
  -yoshidaEndpointA / 3780 - yoshidaEndpointA ^ 3 / 178200 -
    31 * yoshidaEndpointA ^ 5 / 36324288 -
    61 * yoshidaEndpointA ^ 6 / 907200

/-- Twice the degree-six regular-kernel correlation integral in the `P2-P6`
entry. -/
def factorTwoP6EvenRegularGram26 : ℝ :=
  yoshidaEndpointA ^ 3 / 3088800 +
    31 * yoshidaEndpointA ^ 5 / 1362160800

/-- Twice the degree-six regular-kernel correlation integral in the `P4-P4`
entry. -/
def factorTwoP6EvenRegularGram44 : ℝ :=
  yoshidaEndpointA / 4158 + yoshidaEndpointA ^ 3 / 514800 +
    31 * yoshidaEndpointA ^ 5 / 408648240

/-- Twice the degree-six regular-kernel correlation integral in the `P4-P6`
entry. -/
def factorTwoP6EvenRegularGram46 : ℝ :=
  -yoshidaEndpointA / 15444 - yoshidaEndpointA ^ 3 / 2316600 -
    31 * yoshidaEndpointA ^ 5 / 3087564480

/-- Twice the degree-six regular-kernel correlation integral in the `P6-P6`
entry. -/
def factorTwoP6EvenRegularGram66 : ℝ :=
  yoshidaEndpointA / 12870 + 7 * yoshidaEndpointA ^ 3 / 26254800 +
    31 * yoshidaEndpointA ^ 5 / 8799558768

theorem integral_regularKernelPolynomial6_mul_correlation00 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        evenStructuralCorrelation00 t) = factorTwoP6EvenRegularGram00 := by
  unfold yoshidaRegularKernelPolynomial6 evenStructuralCorrelation00
    factorTwoP6EvenRegularGram00
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_regularKernelPolynomial6_mul_correlation02 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        evenStructuralCorrelation02 t) = factorTwoP6EvenRegularGram02 := by
  unfold yoshidaRegularKernelPolynomial6 evenStructuralCorrelation02
    factorTwoP6EvenRegularGram02
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_regularKernelPolynomial6_mul_correlation04 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        factorTwoIntrinsicP4Correlation04 t) = factorTwoP6EvenRegularGram04 := by
  unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP4Correlation04
    factorTwoP6EvenRegularGram04
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_regularKernelPolynomial6_mul_correlation06 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        factorTwoIntrinsicP6Correlation06 t) = factorTwoP6EvenRegularGram06 := by
  unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP6Correlation06
    factorTwoP6EvenRegularGram06
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_regularKernelPolynomial6_mul_correlation22 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        evenStructuralCorrelation22 t) = factorTwoP6EvenRegularGram22 := by
  unfold yoshidaRegularKernelPolynomial6 evenStructuralCorrelation22
    factorTwoP6EvenRegularGram22
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_regularKernelPolynomial6_mul_correlation24 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        factorTwoIntrinsicP4Correlation24 t) = factorTwoP6EvenRegularGram24 := by
  unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP4Correlation24
    factorTwoP6EvenRegularGram24
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_regularKernelPolynomial6_mul_correlation26 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        factorTwoIntrinsicP6Correlation26 t) = factorTwoP6EvenRegularGram26 := by
  unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP6Correlation26
    factorTwoP6EvenRegularGram26
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_regularKernelPolynomial6_mul_correlation44 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        factorTwoIntrinsicP4Correlation44 t) = factorTwoP6EvenRegularGram44 := by
  simpa only [factorTwoP6EvenRegularGram44] using
    integral_regularKernelPolynomial6_mul_p4Correlation44

theorem integral_regularKernelPolynomial6_mul_correlation46 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        factorTwoIntrinsicP6Correlation46 t) = factorTwoP6EvenRegularGram46 := by
  unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP6Correlation46
    factorTwoP6EvenRegularGram46
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

theorem integral_regularKernelPolynomial6_mul_correlation66 :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        factorTwoIntrinsicP6Correlation66 t) = factorTwoP6EvenRegularGram66 := by
  unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP6Correlation66
    factorTwoP6EvenRegularGram66
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) 0 2)
    (Continuous.intervalIntegrable (by fun_prop) 0 2)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [intervalIntegral.integral_const_mul]
  repeat rw [integral_pow]
  norm_num
  ring

/-! ## Exact endpoint-potential entries -/

private theorem intervalIntegrable_endpointPotential_mul_even_pow_local
    (n : ℕ) :
    IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * x ^ (2 * n))
      volume (-1) 1 :=
  intervalIntegrable_endpointPotential_mul (fun x : ℝ ↦ x ^ (2 * n))
    (continuous_id.pow (2 * n))

/-- Exact endpoint-potential `P0-P6` entry. -/
theorem integral_endpointPotential_mul_centeredEvenP0_mul_P6 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredEvenP0 x *
        factorTwoCenteredP6 x) = (1 / 21 : ℝ) := by
  have h0 : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow_local 0
  have h2 := intervalIntegrable_endpointPotential_mul_even_pow_local 1
  have h4 := intervalIntegrable_endpointPotential_mul_even_pow_local 2
  have h6 := intervalIntegrable_endpointPotential_mul_even_pow_local 3
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredEvenP0 x *
        factorTwoCenteredP6 x) =
    fun x ↦ (231 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) -
      (315 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) +
      (105 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) -
      (5 / 16 : ℝ) * yoshidaEndpointPotential x by
    funext x
    unfold centeredEvenP0
    rw [factorTwoCenteredP6_eq]
    ring,
    intervalIntegral.integral_sub
      (((h6.const_mul (231 / 16 : ℝ)).sub
        (h4.const_mul (315 / 16 : ℝ))).add
          (h2.const_mul (105 / 16 : ℝ)))
      (h0.const_mul (5 / 16 : ℝ)),
    intervalIntegral.integral_add
      ((h6.const_mul (231 / 16 : ℝ)).sub
        (h4.const_mul (315 / 16 : ℝ)))
      (h2.const_mul (105 / 16 : ℝ)),
    intervalIntegral.integral_sub
      (h6.const_mul (231 / 16 : ℝ))
      (h4.const_mul (315 / 16 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq, integral_endpointPotential_one]
  ring

/-- Exact endpoint-potential `P2-P6` entry. -/
theorem integral_endpointPotential_mul_centeredEvenP2_mul_P6 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredEvenP2 x *
        factorTwoCenteredP6 x) = (1 / 18 : ℝ) := by
  have h0 : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow_local 0
  have h2 := intervalIntegrable_endpointPotential_mul_even_pow_local 1
  have h4 := intervalIntegrable_endpointPotential_mul_even_pow_local 2
  have h6 := intervalIntegrable_endpointPotential_mul_even_pow_local 3
  have h8 := intervalIntegrable_endpointPotential_mul_even_pow_local 4
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * centeredEvenP2 x *
        factorTwoCenteredP6 x) =
    fun x ↦ (693 / 32 : ℝ) * (yoshidaEndpointPotential x * x ^ 8) -
      (147 / 4 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) +
      (315 / 16 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) -
      (15 / 4 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) +
      (5 / 32 : ℝ) * yoshidaEndpointPotential x by
    funext x
    unfold centeredEvenP2
    rw [factorTwoCenteredP6_eq]
    ring,
    intervalIntegral.integral_add
      ((((h8.const_mul (693 / 32 : ℝ)).sub
        (h6.const_mul (147 / 4 : ℝ))).add
          (h4.const_mul (315 / 16 : ℝ))).sub
            (h2.const_mul (15 / 4 : ℝ)))
      (h0.const_mul (5 / 32 : ℝ)),
    intervalIntegral.integral_sub
      (((h8.const_mul (693 / 32 : ℝ)).sub
        (h6.const_mul (147 / 4 : ℝ))).add
          (h4.const_mul (315 / 16 : ℝ)))
      (h2.const_mul (15 / 4 : ℝ)),
    intervalIntegral.integral_add
      ((h8.const_mul (693 / 32 : ℝ)).sub
        (h6.const_mul (147 / 4 : ℝ)))
      (h4.const_mul (315 / 16 : ℝ)),
    intervalIntegral.integral_sub
      (h8.const_mul (693 / 32 : ℝ))
      (h6.const_mul (147 / 4 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_eight,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq, integral_endpointPotential_one]
  ring

/-- Exact endpoint-potential `P4-P6` entry. -/
theorem integral_endpointPotential_mul_P4_mul_P6 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * factorTwoCenteredP4 x *
        factorTwoCenteredP6 x) = (1 / 11 : ℝ) := by
  have h0 : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa using intervalIntegrable_endpointPotential_mul_even_pow_local 0
  have h2 := intervalIntegrable_endpointPotential_mul_even_pow_local 1
  have h4 := intervalIntegrable_endpointPotential_mul_even_pow_local 2
  have h6 := intervalIntegrable_endpointPotential_mul_even_pow_local 3
  have h8 := intervalIntegrable_endpointPotential_mul_even_pow_local 4
  have h10 := intervalIntegrable_endpointPotential_mul_even_pow_local 5
  rw [show (fun x : ℝ ↦
      yoshidaEndpointPotential x * factorTwoCenteredP4 x *
        factorTwoCenteredP6 x) =
    fun x ↦ (8085 / 128 : ℝ) *
        (yoshidaEndpointPotential x * x ^ 10) -
      (17955 / 128 : ℝ) * (yoshidaEndpointPotential x * x ^ 8) +
      (6909 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 6) -
      (2135 / 64 : ℝ) * (yoshidaEndpointPotential x * x ^ 4) +
      (465 / 128 : ℝ) * (yoshidaEndpointPotential x * x ^ 2) -
      (15 / 128 : ℝ) * yoshidaEndpointPotential x by
    funext x
    unfold factorTwoCenteredP4
    rw [factorTwoCenteredP6_eq]
    ring,
    intervalIntegral.integral_sub
      (((((h10.const_mul (8085 / 128 : ℝ)).sub
        (h8.const_mul (17955 / 128 : ℝ))).add
          (h6.const_mul (6909 / 64 : ℝ))).sub
            (h4.const_mul (2135 / 64 : ℝ))).add
              (h2.const_mul (465 / 128 : ℝ)))
      (h0.const_mul (15 / 128 : ℝ)),
    intervalIntegral.integral_add
      ((((h10.const_mul (8085 / 128 : ℝ)).sub
        (h8.const_mul (17955 / 128 : ℝ))).add
          (h6.const_mul (6909 / 64 : ℝ))).sub
            (h4.const_mul (2135 / 64 : ℝ)))
      (h2.const_mul (465 / 128 : ℝ)),
    intervalIntegral.integral_sub
      (((h10.const_mul (8085 / 128 : ℝ)).sub
        (h8.const_mul (17955 / 128 : ℝ))).add
          (h6.const_mul (6909 / 64 : ℝ)))
      (h4.const_mul (2135 / 64 : ℝ)),
    intervalIntegral.integral_add
      ((h10.const_mul (8085 / 128 : ℝ)).sub
        (h8.const_mul (17955 / 128 : ℝ)))
      (h6.const_mul (6909 / 64 : ℝ)),
    intervalIntegral.integral_sub
      (h10.const_mul (8085 / 128 : ℝ))
      (h8.const_mul (17955 / 128 : ℝ))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [integral_endpointPotential_mul_pow_ten,
    integral_endpointPotential_mul_pow_eight,
    integral_endpointPotential_mul_pow_six,
    integral_endpointPotential_mul_pow_four,
    integral_endpointPotential_mul_sq, integral_endpointPotential_one]
  ring

/-! ## Exact raw-log energy -/

/-- The raw-log Gram on the retained even modes. -/
def factorTwoP6EvenRawLogGram (_c0 c2 c4 c6 : ℝ) : ℝ :=
  (12 / 5 : ℝ) * c2 ^ 2 + (50 / 27 : ℝ) * c4 ^ 2 +
    (98 / 65 : ℝ) * c6 ^ 2

/-- The shifted-Legendre eigenidentity evaluates the entire four-mode raw
form at once. -/
theorem centeredRawLogEnergy_intrinsicEvenP0246
    (c0 c2 c4 c6 : ℝ) :
    centeredRawLogEnergy
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) =
      factorTwoP6EvenRawLogGram c0 c2 c4 c6 := by
  let p : ℝ[X] :=
    c0 • shiftedLegendreReal 0 + c2 • shiftedLegendreReal 2 +
      c4 • shiftedLegendreReal 4 + c6 • shiftedLegendreReal 6
  let pfun : unitInterval → ℝ := fun t ↦ p.eval (t : ℝ)
  let qfun : unitInterval → ℝ := fun t ↦
    centeredPullback
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) (t : ℝ)
  have hmode (t : unitInterval) : qfun t = p.eval (t : ℝ) := by
    dsimp only [qfun, p]
    unfold factorTwoIntrinsicEvenP0246Profile
      factorTwoIntrinsicEvenP024Profile factorTwoIntrinsicSixEvenTail
      factorTwoEvenStructuralLowProfile centeredPullback centeredEvenP0
      centeredEvenP2 factorTwoCenteredP4 factorTwoCenteredP6
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_smul]
    norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
      Polynomial.eval_map, Polynomial.eval_finset_sum,
      Finset.sum_range_succ, Nat.choose]
    ring
  have hpEnergy : Integrable (unitIntervalRawLogEnergyIntegrand pfun) := by
    simpa only [pfun] using
      integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hqEnergy : Integrable (unitIntervalRawLogEnergyIntegrand qfun) := by
    apply hpEnergy.congr
    filter_upwards [] with z
    unfold unitIntervalRawLogEnergyIntegrand
    dsimp only [pfun]
    rw [hmode z.1, hmode z.2]
  have hqP : unitIntervalLogEnergy qfun = unitIntervalLogEnergy pfun := by
    unfold unitIntervalLogEnergy
    apply congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) * z)
    apply integral_congr_ae
    filter_upwards [] with z
    unfold unitIntervalRawLogEnergyIntegrand
    dsimp only [pfun]
    rw [hmode z.1, hmode z.2]
  have hpIdentity : unitIntervalLogEnergy pfun =
      ∫ t : unitInterval,
        p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ) := by
    unfold unitIntervalLogEnergy
    rw [show (∫ z, unitIntervalRawLogEnergyIntegrand pfun z) =
        2 * ∫ t : unitInterval,
          p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ) by
      simpa only [pfun] using
        integral_unitIntervalRawLogEnergyIntegrand_polynomial p]
    ring
  have hpKernel : shiftedLogKernel p =
      c0 • (Polynomial.C 0 * shiftedLegendreReal 0) +
        c2 • (Polynomial.C 3 * shiftedLegendreReal 2) +
        c4 • (Polynomial.C (25 / 6 : ℝ) * shiftedLegendreReal 4) +
        c6 • (Polynomial.C (49 / 10 : ℝ) * shiftedLegendreReal 6) := by
    dsimp only [p]
    rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal,
      shiftedLogKernel_shiftedLegendreReal]
    norm_num [harmonic]
  have hpValue :
      (∫ t : unitInterval,
        p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ)) =
      (3 / 5 : ℝ) * c2 ^ 2 + (25 / 54 : ℝ) * c4 ^ 2 +
        (49 / 130 : ℝ) * c6 ^ 2 := by
    have hintegralLinear (a : ℝ) :
        (∫ x : ℝ in 0..1, a * x) = a / 2 := by
      rw [show (fun x : ℝ ↦ a * x) = fun x ↦ a * x ^ 1 by
        funext x
        ring,
        intervalIntegral.integral_const_mul, integral_pow]
      norm_num
      ring
    rw [hpKernel]
    let q : ℝ[X] :=
      c0 • (Polynomial.C 0 * shiftedLegendreReal 0) +
        c2 • (Polynomial.C 3 * shiftedLegendreReal 2) +
        c4 • (Polynomial.C (25 / 6 : ℝ) * shiftedLegendreReal 4) +
        c6 • (Polynomial.C (49 / 10 : ℝ) * shiftedLegendreReal 6)
    change (∫ t : unitInterval,
      (fun x : ℝ ↦ p.eval x * q.eval x) (t : ℝ)) = _
    calc
      _ = ∫ x : ℝ in 0..1, p.eval x * q.eval x :=
        integral_unitInterval_eq_intervalIntegral _
      _ = _ := by
        dsimp only [p, q]
        simp only [Polynomial.eval_add, Polynomial.eval_smul,
          Polynomial.eval_mul, Polynomial.eval_C, smul_eq_mul]
        norm_num [shiftedLegendreReal, Polynomial.shiftedLegendre,
          Polynomial.eval_map, Polynomial.eval_finset_sum,
          Finset.sum_range_succ, Nat.choose]
        ring_nf
        repeat rw [intervalIntegral.integral_add
          (Continuous.intervalIntegrable (by fun_prop) 0 1)
          (Continuous.intervalIntegrable (by fun_prop) 0 1)]
        repeat rw [intervalIntegral.integral_sub
          (Continuous.intervalIntegrable (by fun_prop) 0 1)
          (Continuous.intervalIntegrable (by fun_prop) 0 1)]
        simp only [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_mul_const, integral_pow, integral_id,
          intervalIntegral.integral_const, smul_eq_mul]
        repeat rw [hintegralLinear]
        norm_num
        ring
  have hbridge := unitIntervalLogEnergy_centeredPullback
    (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) hqEnergy
  change unitIntervalLogEnergy qfun =
    (1 / 4 : ℝ) * centeredRawLogEnergy
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) at hbridge
  rw [hqP, hpIdentity, hpValue] at hbridge
  unfold factorTwoP6EvenRawLogGram
  linarith

/-! ## Aggregate potential and regular-kernel quadratics -/

private theorem integral_ten_add_interval
    (f₀ f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₈ f₉ : ℝ → ℝ)
    (l r : ℝ)
    (h₀ : IntervalIntegrable f₀ volume l r)
    (h₁ : IntervalIntegrable f₁ volume l r)
    (h₂ : IntervalIntegrable f₂ volume l r)
    (h₃ : IntervalIntegrable f₃ volume l r)
    (h₄ : IntervalIntegrable f₄ volume l r)
    (h₅ : IntervalIntegrable f₅ volume l r)
    (h₆ : IntervalIntegrable f₆ volume l r)
    (h₇ : IntervalIntegrable f₇ volume l r)
    (h₈ : IntervalIntegrable f₈ volume l r)
    (h₉ : IntervalIntegrable f₉ volume l r) :
    (∫ t : ℝ in l..r,
      f₀ t + (f₁ t + (f₂ t + (f₃ t + (f₄ t +
        (f₅ t + (f₆ t + (f₇ t + (f₈ t + f₉ t))))))))) =
      (∫ t : ℝ in l..r, f₀ t) +
        ((∫ t : ℝ in l..r, f₁ t) +
          ((∫ t : ℝ in l..r, f₂ t) +
            ((∫ t : ℝ in l..r, f₃ t) +
              ((∫ t : ℝ in l..r, f₄ t) +
                ((∫ t : ℝ in l..r, f₅ t) +
                  ((∫ t : ℝ in l..r, f₆ t) +
                    ((∫ t : ℝ in l..r, f₇ t) +
                      ((∫ t : ℝ in l..r, f₈ t) +
                        (∫ t : ℝ in l..r, f₉ t))))))))) := by
  rw [intervalIntegral.integral_add h₀
      (h₁.add (h₂.add (h₃.add (h₄.add
        (h₅.add (h₆.add (h₇.add (h₈.add h₉)))))))),
    intervalIntegral.integral_add h₁
      (h₂.add (h₃.add (h₄.add
        (h₅.add (h₆.add (h₇.add (h₈.add h₉))))))),
    intervalIntegral.integral_add h₂
      (h₃.add (h₄.add
        (h₅.add (h₆.add (h₇.add (h₈.add h₉)))))),
    intervalIntegral.integral_add h₃
      (h₄.add (h₅.add (h₆.add (h₇.add (h₈.add h₉))))),
    intervalIntegral.integral_add h₄
      (h₅.add (h₆.add (h₇.add (h₈.add h₉)))),
    intervalIntegral.integral_add h₅
      (h₆.add (h₇.add (h₈.add h₉))),
    intervalIntegral.integral_add h₆ (h₇.add (h₈.add h₉)),
    intervalIntegral.integral_add h₇ (h₈.add h₉),
    intervalIntegral.integral_add h₈ h₉]

/-- The exact endpoint-potential Gram on the four retained even modes. -/
def factorTwoP6EvenPotentialGram (c0 c2 c4 c6 : ℝ) : ℝ :=
  (2 - 2 * Real.log 2) * c0 ^ 2 +
    2 * (1 / 3 : ℝ) * c0 * c2 +
    2 * (1 / 10 : ℝ) * c0 * c4 +
    2 * (1 / 21 : ℝ) * c0 * c6 +
    (41 / 75 - (2 / 5 : ℝ) * Real.log 2) * c2 ^ 2 +
    2 * (1 / 7 : ℝ) * c2 * c4 +
    2 * (1 / 18 : ℝ) * c2 * c6 +
    (1739 / 5670 - (2 / 9 : ℝ) * Real.log 2) * c4 ^ 2 +
    2 * (1 / 11 : ℝ) * c4 * c6 +
    (249251 / 1171170 - (2 / 13 : ℝ) * Real.log 2) * c6 ^ 2

/-- Exact evaluation of the endpoint-potential term on the genuine
`P0/P2/P4/P6` profile. -/
theorem integral_endpointPotential_mul_intrinsicEvenP0246_sq
    (c0 c2 c4 c6 : ℝ) :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x *
        factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x ^ 2) =
      factorTwoP6EvenPotentialGram c0 c2 c4 c6 := by
  have hP0 : Continuous centeredEvenP0 := by
    unfold centeredEvenP0
    fun_prop
  have hP2 : Continuous centeredEvenP2 := by
    unfold centeredEvenP2
    fun_prop
  have hP4 := continuous_factorTwoCenteredP4
  have hP6 := continuous_factorTwoCenteredP6
  have h00 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredEvenP0 x ^ 2)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq centeredEvenP0 hP0
  have h02 := intervalIntegrable_endpointPotential_mul
    centeredEvenP0 centeredEvenP2 hP0 hP2
  have h04 := intervalIntegrable_endpointPotential_mul
    centeredEvenP0 factorTwoCenteredP4 hP0 hP4
  have h06 := intervalIntegrable_endpointPotential_mul
    centeredEvenP0 factorTwoCenteredP6 hP0 hP6
  have h22 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * centeredEvenP2 x ^ 2)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq centeredEvenP2 hP2
  have h24 := intervalIntegrable_endpointPotential_mul
    centeredEvenP2 factorTwoCenteredP4 hP2 hP4
  have h26 := intervalIntegrable_endpointPotential_mul
    centeredEvenP2 factorTwoCenteredP6 hP2 hP6
  have h44 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * factorTwoCenteredP4 x ^ 2)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq factorTwoCenteredP4 hP4
  have h46 := intervalIntegrable_endpointPotential_mul
    factorTwoCenteredP4 factorTwoCenteredP6 hP4 hP6
  have h66 : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointPotential x * factorTwoCenteredP6 x ^ 2)
      volume (-1) 1 :=
    intervalIntegrable_endpointPotential_mul_sq factorTwoCenteredP6 hP6
  rw [show (fun x : ℝ ↦ yoshidaEndpointPotential x *
      factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x ^ 2) =
    fun x ↦
      c0 ^ 2 * (yoshidaEndpointPotential x * centeredEvenP0 x ^ 2) +
      ((2 * c0 * c2) *
          (yoshidaEndpointPotential x * centeredEvenP0 x * centeredEvenP2 x) +
      ((2 * c0 * c4) *
          (yoshidaEndpointPotential x * centeredEvenP0 x * factorTwoCenteredP4 x) +
      ((2 * c0 * c6) *
          (yoshidaEndpointPotential x * centeredEvenP0 x * factorTwoCenteredP6 x) +
      (c2 ^ 2 * (yoshidaEndpointPotential x * centeredEvenP2 x ^ 2) +
      ((2 * c2 * c4) *
          (yoshidaEndpointPotential x * centeredEvenP2 x * factorTwoCenteredP4 x) +
      ((2 * c2 * c6) *
          (yoshidaEndpointPotential x * centeredEvenP2 x * factorTwoCenteredP6 x) +
      (c4 ^ 2 * (yoshidaEndpointPotential x * factorTwoCenteredP4 x ^ 2) +
      ((2 * c4 * c6) *
          (yoshidaEndpointPotential x * factorTwoCenteredP4 x * factorTwoCenteredP6 x) +
      c6 ^ 2 * (yoshidaEndpointPotential x * factorTwoCenteredP6 x ^ 2))))))))) by
    funext x
    unfold factorTwoIntrinsicEvenP0246Profile
      factorTwoIntrinsicEvenP024Profile factorTwoIntrinsicSixEvenTail
      factorTwoEvenStructuralLowProfile
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring]
  rw [integral_ten_add_interval _ _ _ _ _ _ _ _ _ _ (-1) 1
    (h00.const_mul (c0 ^ 2))
    (h02.const_mul (2 * c0 * c2))
    (h04.const_mul (2 * c0 * c4))
    (h06.const_mul (2 * c0 * c6))
    (h22.const_mul (c2 ^ 2))
    (h24.const_mul (2 * c2 * c4))
    (h26.const_mul (2 * c2 * c6))
    (h44.const_mul (c4 ^ 2))
    (h46.const_mul (2 * c4 * c6))
    (h66.const_mul (c6 ^ 2))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [show (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredEvenP0 x ^ 2) =
        2 - 2 * Real.log 2 by
      simpa only [centeredEvenP0, one_pow, mul_one] using
        integral_endpointPotential_one,
    show (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * centeredEvenP0 x * centeredEvenP2 x) =
        1 / 3 by
      simpa only [centeredEvenP0, mul_one, one_mul] using
        integral_endpointPotential_mul_centeredEvenP2,
    integral_endpointPotential_mul_centeredEvenP0_mul_P4,
    integral_endpointPotential_mul_centeredEvenP0_mul_P6,
    integral_endpointPotential_mul_centeredEvenP2_sq,
    integral_endpointPotential_mul_centeredEvenP2_mul_P4,
    integral_endpointPotential_mul_centeredEvenP2_mul_P6,
    integral_endpointPotential_mul_factorTwoCenteredP4_sq,
    integral_endpointPotential_mul_P4_mul_P6,
    integral_endpointPotential_mul_factorTwoCenteredP6_sq]
  unfold factorTwoP6EvenPotentialGram
  ring

/-- The exact degree-six regular-kernel Gram on the four retained even
modes. -/
def factorTwoP6EvenRegularGram (c0 c2 c4 c6 : ℝ) : ℝ :=
  factorTwoP6EvenRegularGram00 * c0 ^ 2 +
    2 * factorTwoP6EvenRegularGram02 * c0 * c2 +
    2 * factorTwoP6EvenRegularGram04 * c0 * c4 +
    2 * factorTwoP6EvenRegularGram06 * c0 * c6 +
    factorTwoP6EvenRegularGram22 * c2 ^ 2 +
    2 * factorTwoP6EvenRegularGram24 * c2 * c4 +
    2 * factorTwoP6EvenRegularGram26 * c2 * c6 +
    factorTwoP6EvenRegularGram44 * c4 ^ 2 +
    2 * factorTwoP6EvenRegularGram46 * c4 * c6 +
    factorTwoP6EvenRegularGram66 * c6 ^ 2

/-- Exact evaluation of the degree-six regular-kernel quadratic on the
genuine four-mode profile. -/
theorem integral_regularKernelPolynomial6_mul_intrinsicEvenP0246Correlation
    (c0 c2 c4 c6 : ℝ) :
    2 * (∫ t : ℝ in 0..2,
      yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t) *
        centeredEndpointCorrelation
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) t) =
      factorTwoP6EvenRegularGram c0 c2 c4 c6 := by
  let K : ℝ → ℝ := fun t ↦
    yoshidaRegularKernelPolynomial6 (yoshidaEndpointA * t)
  have h00 : IntervalIntegrable
      (fun t : ℝ ↦ K t * evenStructuralCorrelation00 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [K]
    unfold yoshidaRegularKernelPolynomial6 evenStructuralCorrelation00
    fun_prop
  have h02 : IntervalIntegrable
      (fun t : ℝ ↦ K t * evenStructuralCorrelation02 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [K]
    unfold yoshidaRegularKernelPolynomial6 evenStructuralCorrelation02
    fun_prop
  have h04 : IntervalIntegrable
      (fun t : ℝ ↦ K t * factorTwoIntrinsicP4Correlation04 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [K]
    unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP4Correlation04
    fun_prop
  have h06 : IntervalIntegrable
      (fun t : ℝ ↦ K t * factorTwoIntrinsicP6Correlation06 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [K]
    unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP6Correlation06
    fun_prop
  have h22 : IntervalIntegrable
      (fun t : ℝ ↦ K t * evenStructuralCorrelation22 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [K]
    unfold yoshidaRegularKernelPolynomial6 evenStructuralCorrelation22
    fun_prop
  have h24 : IntervalIntegrable
      (fun t : ℝ ↦ K t * factorTwoIntrinsicP4Correlation24 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [K]
    unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP4Correlation24
    fun_prop
  have h26 : IntervalIntegrable
      (fun t : ℝ ↦ K t * factorTwoIntrinsicP6Correlation26 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [K]
    unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP6Correlation26
    fun_prop
  have h44 : IntervalIntegrable
      (fun t : ℝ ↦ K t * factorTwoIntrinsicP4Correlation44 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [K]
    unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP4Correlation44
    fun_prop
  have h46 : IntervalIntegrable
      (fun t : ℝ ↦ K t * factorTwoIntrinsicP6Correlation46 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [K]
    unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP6Correlation46
    fun_prop
  have h66 : IntervalIntegrable
      (fun t : ℝ ↦ K t * factorTwoIntrinsicP6Correlation66 t) volume 0 2 := by
    apply Continuous.intervalIntegrable
    dsimp only [K]
    unfold yoshidaRegularKernelPolynomial6 factorTwoIntrinsicP6Correlation66
    fun_prop
  have h00v : (∫ t : ℝ in 0..2,
      K t * evenStructuralCorrelation00 t) =
        factorTwoP6EvenRegularGram00 / 2 := by
    dsimp only [K]
    linarith [integral_regularKernelPolynomial6_mul_correlation00]
  have h02v : (∫ t : ℝ in 0..2,
      K t * evenStructuralCorrelation02 t) =
        factorTwoP6EvenRegularGram02 / 2 := by
    dsimp only [K]
    linarith [integral_regularKernelPolynomial6_mul_correlation02]
  have h04v : (∫ t : ℝ in 0..2,
      K t * factorTwoIntrinsicP4Correlation04 t) =
        factorTwoP6EvenRegularGram04 / 2 := by
    dsimp only [K]
    linarith [integral_regularKernelPolynomial6_mul_correlation04]
  have h06v : (∫ t : ℝ in 0..2,
      K t * factorTwoIntrinsicP6Correlation06 t) =
        factorTwoP6EvenRegularGram06 / 2 := by
    dsimp only [K]
    linarith [integral_regularKernelPolynomial6_mul_correlation06]
  have h22v : (∫ t : ℝ in 0..2,
      K t * evenStructuralCorrelation22 t) =
        factorTwoP6EvenRegularGram22 / 2 := by
    dsimp only [K]
    linarith [integral_regularKernelPolynomial6_mul_correlation22]
  have h24v : (∫ t : ℝ in 0..2,
      K t * factorTwoIntrinsicP4Correlation24 t) =
        factorTwoP6EvenRegularGram24 / 2 := by
    dsimp only [K]
    linarith [integral_regularKernelPolynomial6_mul_correlation24]
  have h26v : (∫ t : ℝ in 0..2,
      K t * factorTwoIntrinsicP6Correlation26 t) =
        factorTwoP6EvenRegularGram26 / 2 := by
    dsimp only [K]
    linarith [integral_regularKernelPolynomial6_mul_correlation26]
  have h44v : (∫ t : ℝ in 0..2,
      K t * factorTwoIntrinsicP4Correlation44 t) =
        factorTwoP6EvenRegularGram44 / 2 := by
    dsimp only [K]
    linarith [integral_regularKernelPolynomial6_mul_correlation44]
  have h46v : (∫ t : ℝ in 0..2,
      K t * factorTwoIntrinsicP6Correlation46 t) =
        factorTwoP6EvenRegularGram46 / 2 := by
    dsimp only [K]
    linarith [integral_regularKernelPolynomial6_mul_correlation46]
  have h66v : (∫ t : ℝ in 0..2,
      K t * factorTwoIntrinsicP6Correlation66 t) =
        factorTwoP6EvenRegularGram66 / 2 := by
    dsimp only [K]
    linarith [integral_regularKernelPolynomial6_mul_correlation66]
  change 2 * (∫ t : ℝ in 0..2,
    K t * centeredEndpointCorrelation
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) t) = _
  rw [show (fun t : ℝ ↦ K t * centeredEndpointCorrelation
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) t) =
    fun t ↦
      c0 ^ 2 * (K t * evenStructuralCorrelation00 t) +
      ((2 * c0 * c2) * (K t * evenStructuralCorrelation02 t) +
      ((2 * c0 * c4) * (K t * factorTwoIntrinsicP4Correlation04 t) +
      ((2 * c0 * c6) * (K t * factorTwoIntrinsicP6Correlation06 t) +
      (c2 ^ 2 * (K t * evenStructuralCorrelation22 t) +
      ((2 * c2 * c4) * (K t * factorTwoIntrinsicP4Correlation24 t) +
      ((2 * c2 * c6) * (K t * factorTwoIntrinsicP6Correlation26 t) +
      (c4 ^ 2 * (K t * factorTwoIntrinsicP4Correlation44 t) +
      ((2 * c4 * c6) * (K t * factorTwoIntrinsicP6Correlation46 t) +
      c6 ^ 2 * (K t * factorTwoIntrinsicP6Correlation66 t))))))))) by
    funext t
    rw [centeredEndpointCorrelation_intrinsicEvenP0246]
    ring]
  rw [integral_ten_add_interval _ _ _ _ _ _ _ _ _ _ 0 2
    (h00.const_mul (c0 ^ 2))
    (h02.const_mul (2 * c0 * c2))
    (h04.const_mul (2 * c0 * c4))
    (h06.const_mul (2 * c0 * c6))
    (h22.const_mul (c2 ^ 2))
    (h24.const_mul (2 * c2 * c4))
    (h26.const_mul (2 * c2 * c6))
    (h44.const_mul (c4 ^ 2))
    (h46.const_mul (2 * c4 * c6))
    (h66.const_mul (c6 ^ 2))]
  repeat rw [intervalIntegral.integral_const_mul]
  rw [h00v, h02v, h04v, h06v, h22v, h24v, h26v, h44v, h46v, h66v]
  unfold factorTwoP6EvenRegularGram
  ring

/-! ## The exact non-hyperbolic clean Gram -/

/-- Clean non-hyperbolic `P0-P0` entry. -/
def factorTwoP6EvenCleanPolynomialGram00 : ℝ :=
  2 - 2 * Real.log 2 - 2 * yoshidaEndpointScalarMassLoss -
    yoshidaEndpointA * factorTwoP6EvenRegularGram00

/-- Clean non-hyperbolic `P0-P2` entry. -/
def factorTwoP6EvenCleanPolynomialGram02 : ℝ :=
  1 / 3 - yoshidaEndpointA * factorTwoP6EvenRegularGram02

/-- Clean non-hyperbolic `P0-P4` entry. -/
def factorTwoP6EvenCleanPolynomialGram04 : ℝ :=
  1 / 10 - yoshidaEndpointA * factorTwoP6EvenRegularGram04

/-- Clean non-hyperbolic `P0-P6` entry. -/
def factorTwoP6EvenCleanPolynomialGram06 : ℝ :=
  1 / 21 - yoshidaEndpointA * factorTwoP6EvenRegularGram06

/-- Clean non-hyperbolic `P2-P2` entry. -/
def factorTwoP6EvenCleanPolynomialGram22 : ℝ :=
  3 / 5 + (41 / 75 - (2 / 5 : ℝ) * Real.log 2) -
    (2 / 5 : ℝ) * yoshidaEndpointScalarMassLoss -
    yoshidaEndpointA * factorTwoP6EvenRegularGram22

/-- Clean non-hyperbolic `P2-P4` entry. -/
def factorTwoP6EvenCleanPolynomialGram24 : ℝ :=
  1 / 7 - yoshidaEndpointA * factorTwoP6EvenRegularGram24

/-- Clean non-hyperbolic `P2-P6` entry. -/
def factorTwoP6EvenCleanPolynomialGram26 : ℝ :=
  1 / 18 - yoshidaEndpointA * factorTwoP6EvenRegularGram26

/-- Clean non-hyperbolic `P4-P4` entry. -/
def factorTwoP6EvenCleanPolynomialGram44 : ℝ :=
  25 / 54 + (1739 / 5670 - (2 / 9 : ℝ) * Real.log 2) -
    (2 / 9 : ℝ) * yoshidaEndpointScalarMassLoss -
    yoshidaEndpointA * factorTwoP6EvenRegularGram44

/-- Clean non-hyperbolic `P4-P6` entry. -/
def factorTwoP6EvenCleanPolynomialGram46 : ℝ :=
  1 / 11 - yoshidaEndpointA * factorTwoP6EvenRegularGram46

/-- Clean non-hyperbolic `P6-P6` entry. -/
def factorTwoP6EvenCleanPolynomialGram66 : ℝ :=
  49 / 130 + (249251 / 1171170 - (2 / 13 : ℝ) * Real.log 2) -
    (2 / 13 : ℝ) * yoshidaEndpointScalarMassLoss -
    yoshidaEndpointA * factorTwoP6EvenRegularGram66

/-- The standard polarization of the exact clean non-hyperbolic entries in
the coordinate order `P0,P2,P4,P6`. -/
def factorTwoP6EvenCleanPolynomialGram (c0 c2 c4 c6 : ℝ) : ℝ :=
  factorTwoP6EvenCleanPolynomialGram00 * c0 ^ 2 +
    2 * factorTwoP6EvenCleanPolynomialGram02 * c0 * c2 +
    2 * factorTwoP6EvenCleanPolynomialGram04 * c0 * c4 +
    2 * factorTwoP6EvenCleanPolynomialGram06 * c0 * c6 +
    factorTwoP6EvenCleanPolynomialGram22 * c2 ^ 2 +
    2 * factorTwoP6EvenCleanPolynomialGram24 * c2 * c4 +
    2 * factorTwoP6EvenCleanPolynomialGram26 * c2 * c6 +
    factorTwoP6EvenCleanPolynomialGram44 * c4 ^ 2 +
    2 * factorTwoP6EvenCleanPolynomialGram46 * c4 * c6 +
    factorTwoP6EvenCleanPolynomialGram66 * c6 ^ 2

/-- Removing the exact hyperbolic term from the clean profile model leaves
precisely the displayed four-coordinate Gram quadratic. -/
theorem factorTwoP6EvenNonHyperbolicCleanPolynomialModel_intrinsicEvenP0246_eq_gram
    (c0 c2 c4 c6 : ℝ) :
    factorTwoP6EvenCleanPolynomialModel
        (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) -
      yoshidaEndpointHyperbolicQuadratic
        (fun x ↦
          (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x : ℂ)) =
      factorTwoP6EvenCleanPolynomialGram c0 c2 c4 c6 := by
  have henergy :
      (∫ x : ℝ in -1..1,
        factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6 x ^ 2) =
      2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2 + (2 / 13 : ℝ) * c6 ^ 2 := by
    change factorTwoIntrinsicEnergy
      (factorTwoIntrinsicEvenP0246Profile c0 c2 c4 c6) = _
    exact factorTwoIntrinsicEnergy_intrinsicEvenP0246 c0 c2 c4 c6
  unfold factorTwoP6EvenCleanPolynomialModel
  rw [centeredRawLogEnergy_intrinsicEvenP0246,
    integral_endpointPotential_mul_intrinsicEvenP0246_sq,
    henergy,
    integral_regularKernelPolynomial6_mul_intrinsicEvenP0246Correlation]
  unfold factorTwoP6EvenCleanPolynomialGram
    factorTwoP6EvenCleanPolynomialGram00
    factorTwoP6EvenCleanPolynomialGram02
    factorTwoP6EvenCleanPolynomialGram04
    factorTwoP6EvenCleanPolynomialGram06
    factorTwoP6EvenCleanPolynomialGram22
    factorTwoP6EvenCleanPolynomialGram24
    factorTwoP6EvenCleanPolynomialGram26
    factorTwoP6EvenCleanPolynomialGram44
    factorTwoP6EvenCleanPolynomialGram46
    factorTwoP6EvenCleanPolynomialGram66
    factorTwoP6EvenRawLogGram factorTwoP6EvenPotentialGram
    factorTwoP6EvenRegularGram
  ring

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP6EvenCleanPolynomialGramStructural
