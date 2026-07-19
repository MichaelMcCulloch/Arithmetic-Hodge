import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointReduction
import ArithmeticHodge.Analysis.YoshidaFourCellEvenCapacityStructural
import ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshRegularStructural

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshCoupledCoreStructural

noncomputable section

open UnitIntervalLogEnergyAffine
open ThreeByThreeRankOneSchur
open YoshidaEndpointEvenLowProfile
open YoshidaEndpointEvenStructuralReduction
open YoshidaConstantBounds
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicElevenRetainedP024Structural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRetainedSingularGapStructural
open YoshidaFactorTwoPhaseIntrinsicSixP4EndpointProfile
open YoshidaFactorTwoPhaseIntrinsicSixP4MinusEndpointReduction
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreFourFiveStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseSingularWeightedCauchyStructural
open YoshidaFourCellEvenCapacityStructural
open YoshidaFourCellEvenZeroCoshRegularStructural
open YoshidaFourCellEndpointVarianceStructural
open YoshidaFourCellParityHalfFoldStructural

/-!
# The infinite even tail of the zero-cosh coupled core

The adverse endpoint translation and the logarithmic endpoint potential are
kept as one positive capacity block.  Once the `P₀/P₂/P₄` coordinates
have been removed, the sixth shifted-Legendre harmonic gap alone is already
strictly stronger than the `33 / 20` coupled-core target.  Thus the unresolved
part of the zero-cosh problem is a finite low block and its cross with this
infinite tail, rather than the tail itself.
-/

private theorem integral_polynomial_ten
    (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ l r : ℝ) :
    (∫ x : ℝ in l..r,
      a₀ * x ^ 0 + a₁ * x ^ 1 + a₂ * x ^ 2 + a₃ * x ^ 3 + a₄ * x ^ 4 +
        a₅ * x ^ 5 + a₆ * x ^ 6 + a₇ * x ^ 7 + a₈ * x ^ 8 +
          a₉ * x ^ 9 + a₁₀ * x ^ 10) =
      a₀ * (r - l) + a₁ * (r ^ 2 - l ^ 2) / 2 +
        a₂ * (r ^ 3 - l ^ 3) / 3 + a₃ * (r ^ 4 - l ^ 4) / 4 +
          a₄ * (r ^ 5 - l ^ 5) / 5 + a₅ * (r ^ 6 - l ^ 6) / 6 +
            a₆ * (r ^ 7 - l ^ 7) / 7 + a₇ * (r ^ 8 - l ^ 8) / 8 +
              a₈ * (r ^ 9 - l ^ 9) / 9 + a₉ * (r ^ 10 - l ^ 10) / 10 +
                a₁₀ * (r ^ 11 - l ^ 11) / 11 := by
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) l r)
    (Continuous.intervalIntegrable (by fun_prop) l r)]
  repeat rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- Exact retained dyadic translation on the genuine even `P₀/P₂/P₄`
profile.  In particular, the prime row is not replaced by an independent
operator-norm estimate. -/
theorem fourCellEndpointPairing_intrinsicEvenP024Profile
    (c0 c2 c4 : ℝ) :
    fourCellEndpointPairing
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4) =
      (2 / 5 : ℝ) * c0 ^ 2 + (48 / 125 : ℝ) * c0 * c2 -
        (144 / 3125 : ℝ) * c0 * c4 +
        (962 / 15625 : ℝ) * c2 ^ 2 -
        (8144 / 78125 : ℝ) * c2 * c4 -
        (164582 / 3515625 : ℝ) * c4 ^ 2 := by
  unfold fourCellEndpointPairing factorTwoIntrinsicEvenP024Profile
    factorTwoEvenStructuralLowProfile factorTwoIntrinsicSixEvenTail
    centeredEvenP0 centeredEvenP2 factorTwoCenteredP4
  simp only [Pi.add_apply]
  rw [show (fun x : ℝ ↦
      (c0 * 1 + c2 * ((3 * x ^ 2 - 1) / 2) +
          c4 * ((35 * x ^ 4 - 30 * x ^ 2 + 3) / 8)) *
        (c0 * 1 + c2 * ((3 * (x - 8 / 5) ^ 2 - 1) / 2) +
          c4 * ((35 * (x - 8 / 5) ^ 4 -
            30 * (x - 8 / 5) ^ 2 + 3) / 8))) =
      (fun x ↦
        ((58341 / 8000 : ℝ) * c4 ^ 2 - (8471 / 1000 : ℝ) * c2 * c4 -
            (167 / 100 : ℝ) * c2 ^ 2 + (9911 / 500 : ℝ) * c0 * c4 +
            (71 / 25 : ℝ) * c0 * c2 + c0 ^ 2) * x ^ 0 +
        (-(1119 / 50 : ℝ) * c4 ^ 2 + (701 / 25 : ℝ) * c2 * c4 +
            (12 / 5 : ℝ) * c2 ^ 2 - (1492 / 25 : ℝ) * c0 * c4 -
            (24 / 5 : ℝ) * c0 * c2) * x ^ 1 +
        (-(19653 / 400 : ℝ) * c4 ^ 2 - (14517 / 1000 : ℝ) * c2 * c4 +
            (213 / 50 : ℝ) * c2 ^ 2 + (597 / 10 : ℝ) * c0 * c4 +
            3 * c0 * c2) * x ^ 2 +
        ((2133 / 10 : ℝ) * c4 ^ 2 - (1438 / 25 : ℝ) * c2 * c4 -
            (36 / 5 : ℝ) * c2 ^ 2 - 28 * c0 * c4) * x ^ 3 +
        (-(120973 / 800 : ℝ) * c4 ^ 2 + (4079 / 40 : ℝ) * c2 * c4 +
            (9 / 4 : ℝ) * c2 ^ 2 + (35 / 4 : ℝ) * c0 * c4) * x ^ 4 +
        (-(1561 / 10 : ℝ) * c4 ^ 2 - 63 * c2 * c4) * x ^ 5 +
        ((4179 / 16 : ℝ) * c4 ^ 2 + (105 / 8 : ℝ) * c2 * c4) * x ^ 6 +
        (-(245 / 2 : ℝ) * c4 ^ 2) * x ^ 7 +
        (1225 / 64 : ℝ) * c4 ^ 2 * x ^ 8 + 0 * x ^ 9 + 0 * x ^ 10) by
      funext x
      ring,
    integral_polynomial_ten]
  norm_num
  ring

/-- The exact raw-plus-potential Gram on the low even profile.  This is
deduced from the retained singular square, so the logarithmic potential and
raw kernel remain one structural identity. -/
theorem raw_div_four_add_potential_add_logMass_intrinsicEvenP024Profile
    (c0 c2 c4 : ℝ) :
    centeredRawLogEnergy
          (factorTwoIntrinsicEvenP024Profile c0 c2 c4) / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x *
          factorTwoIntrinsicEvenP024Profile c0 c2 c4 x ^ 2) +
        Real.log 2 *
          (∫ x : ℝ in -1..1,
            factorTwoIntrinsicEvenP024Profile c0 c2 c4 x ^ 2) =
      symmetricQuadratic
        2 (1 / 3) (1 / 10) (86 / 75) (1 / 7) (2182 / 2835)
        c0 c2 c4 := by
  let w : ℝ → ℝ := factorTwoIntrinsicEvenP024Profile c0 c2 c4
  have hw : Continuous w := by
    simpa only [w] using
      factorTwoIntrinsicEvenP024Profile_continuous c0 c2 c4
  have hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w := by
    simpa only [w] using
      factorTwoIntrinsicEvenP024Profile_locallyLipschitzOn c0 c2 c4
  have hs := half_singularWeightedEnergy_eq_protected_add_logMass
    w (0 : ℝ → ℝ) hw continuous_zero hlocal
      (by
        have hd : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
        change LocallyLipschitzOn (Icc (-1 : ℝ) 1) (fun _ : ℝ ↦ (0 : ℝ))
        exact hd.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1))
      0 0
  have hzero :=
    half_singularWeightedEnergy_intrinsicEvenP024_zero c0 c2 c4
  have h0raw : centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
    unfold centeredRawLogEnergy
    simp
  change (1 / 2 : ℝ) *
      factorTwoPhaseSingularWeightedEnergy w (0 : ℝ → ℝ) 0 0 = _
    at hzero
  unfold factorTwoIntrinsicProtectedBlock factorTwoIntrinsicEnergy
    factorTwoIntrinsicPotentialEnergy at hs
  simp [factorTwoCenteredPhaseCorrelation,
    factorTwoCenteredCrossCorrelation] at hs
  rw [h0raw] at hs
  norm_num at hs hzero
  simpa only [w] using hs.symm.trans hzero

/-- Exact coupled-core quadratic on the low even profile.  The last line is
the exact dyadic prime Gram, not a separately estimated prime loss. -/
theorem fourCellEvenZeroCoshCoupledCore_intrinsicEvenP024Profile_eq_quadratic
    (c0 c2 c4 : ℝ) :
    fourCellEvenZeroCoshCoupledCore
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4) =
      symmetricQuadratic
          2 (1 / 3) (1 / 10) (86 / 75) (1 / 7) (2182 / 2835)
          c0 c2 c4 -
        Real.log 2 *
          (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
            (2 / 9 : ℝ) * c4 ^ 2) -
        Real.sqrt 2 * Real.log 2 *
          ((2 / 5 : ℝ) * c0 ^ 2 + (48 / 125 : ℝ) * c0 * c2 -
            (144 / 3125 : ℝ) * c0 * c4 +
            (962 / 15625 : ℝ) * c2 ^ 2 -
            (8144 / 78125 : ℝ) * c2 * c4 -
            (164582 / 3515625 : ℝ) * c4 ^ 2) := by
  have henergy :=
    raw_div_four_add_potential_add_logMass_intrinsicEvenP024Profile
      c0 c2 c4
  have hmass := integral_factorTwoIntrinsicEvenP024Profile_sq c0 c2 c4
  have hpair :=
    fourCellEndpointPairing_intrinsicEvenP024Profile c0 c2 c4
  unfold fourCellEvenZeroCoshCoupledCore
  rw [hmass] at henergy
  rw [hpair]
  linarith

set_option maxHeartbeats 600000 in
/-- The complete low `P₀/P₂/P₄` coupled core clears `33 / 20` on
the same narrow constant cone forced by the zero-wide-cosh condition.  This
is a three-coordinate Schur estimate for the joint raw/potential/prime Gram;
no list of test profiles and no independent prime payment is used. -/
theorem thirtyThree_div_twenty_mass_le_coupledCore_intrinsicEvenP024_of_constant_small
    (c0 c2 c4 : ℝ)
    (hconstant : c0 ^ 2 ≤ (1 / 4000 : ℝ) *
      (2 * c0 ^ 2 + (2 / 5 : ℝ) * c2 ^ 2 +
        (2 / 9 : ℝ) * c4 ^ 2)) :
    (33 / 20 : ℝ) *
        (∫ x : ℝ in -1..1,
          factorTwoIntrinsicEvenP024Profile c0 c2 c4 x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore
        (factorTwoIntrinsicEvenP024Profile c0 c2 c4) := by
  let beta : ℝ := Real.sqrt 2 * Real.log 2
  let N : ℝ := (2 / 5 : ℝ) * c2 ^ 2 + (2 / 9 : ℝ) * c4 ^ 2
  let A00 : ℝ :=
    2 - 2 * Real.log 2 - (2 / 5 : ℝ) * beta - 33 / 10
  let A22 : ℝ :=
    86 / 75 - (2 / 5 : ℝ) * Real.log 2 -
      (962 / 15625 : ℝ) * beta - 33 / 50
  let A44 : ℝ :=
    2182 / 2835 - (2 / 9 : ℝ) * Real.log 2 +
      (164582 / 3515625 : ℝ) * beta - 11 / 30
  let C02 : ℝ := 2 / 3 - (48 / 125 : ℝ) * beta
  let C04 : ℝ := 1 / 5 + (144 / 3125 : ℝ) * beta
  let C24 : ℝ := 2 / 7 + (8144 / 78125 : ℝ) * beta
  have hlogLower := strict_log_two_bounds.1
  have hlogUpper := strict_log_two_bounds.2
  have hsqrtLower := sqrt_two_kernel_bounds.1
  have hsqrtUpper := sqrt_two_kernel_bounds.2
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbeta0 : 0 ≤ beta := by
    dsimp only [beta]
    positivity
  have hbeta : beta ≤ (981 / 1000 : ℝ) := by
    dsimp only [beta]
    have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hfirst : Real.sqrt 2 * Real.log 2 <
        (70711 / 50000 : ℝ) * Real.log 2 :=
      mul_lt_mul_of_pos_right hsqrtUpper hlogPos
    have hsecond : (70711 / 50000 : ℝ) * Real.log 2 <
        (70711 / 50000 : ℝ) * (6932 / 10000 : ℝ) :=
      mul_lt_mul_of_pos_left hlogUpper (by norm_num)
    norm_num at hfirst hsecond ⊢
    linarith
  have hbetaLower : (49 / 50 : ℝ) ≤ beta := by
    dsimp only [beta]
    have hproduct :
        (141421 / 100000 : ℝ) * (6931 / 10000 : ℝ) <
          Real.sqrt 2 * Real.log 2 := by
      calc
        (141421 / 100000 : ℝ) * (6931 / 10000 : ℝ) <
            Real.sqrt 2 * (6931 / 10000 : ℝ) :=
          mul_lt_mul_of_pos_right hsqrtLower (by norm_num)
        _ < Real.sqrt 2 * Real.log 2 :=
          mul_lt_mul_of_pos_left hlogLower
            (Real.sqrt_pos.2 (by norm_num))
    norm_num at hproduct ⊢
    linarith
  have hA00 : (-31 / 10 : ℝ) ≤ A00 := by
    dsimp only [A00]
    nlinarith
  have hA22 : (1489 / 10000 : ℝ) ≤ A22 := by
    dsimp only [A22]
    nlinarith
  have hA44 : (2948 / 10000 : ℝ) ≤ A44 := by
    dsimp only [A44]
    nlinarith only [hlogUpper, hbetaLower]
  have hC02 : 0 ≤ C02 := by
    dsimp only [C02]
    nlinarith
  have hC02Upper : C02 ≤ (2 / 3 : ℝ) := by
    dsimp only [C02]
    nlinarith
  have hC04 : 0 ≤ C04 := by
    dsimp only [C04]
    nlinarith
  have hC04Upper : C04 ≤ (1 / 4 : ℝ) := by
    dsimp only [C04]
    nlinarith
  have hC24 : 0 ≤ C24 := by
    dsimp only [C24]
    nlinarith
  have hC24Upper : C24 ≤ (19399 / 50000 : ℝ) := by
    dsimp only [C24]
    nlinarith
  have hcross02 :
      -(28 * c0 ^ 2 + (1 / 250 : ℝ) * c2 ^ 2) ≤
        C02 * c0 * c2 := by
    by_cases hp : 0 ≤ c0 * c2
    · have hnonneg : 0 ≤ C02 * (c0 * c2) :=
        mul_nonneg hC02 hp
      calc
        -(28 * c0 ^ 2 + (1 / 250 : ℝ) * c2 ^ 2) ≤ 0 := by
          nlinarith only [sq_nonneg c0, sq_nonneg c2]
        _ ≤ C02 * c0 * c2 := by simpa only [mul_assoc] using hnonneg
    · have hp' : c0 * c2 < 0 := lt_of_not_ge hp
      have hcompare : (2 / 3 : ℝ) * (c0 * c2) ≤
          C02 * (c0 * c2) :=
        mul_le_mul_of_nonpos_right hC02Upper hp'.le
      have hsquare := sq_nonneg (84 * c0 + c2)
      have hyoung :
          -(28 * c0 ^ 2 + (1 / 250 : ℝ) * c2 ^ 2) ≤
            (2 / 3 : ℝ) * (c0 * c2) := by
        nlinarith only [hsquare, sq_nonneg c2]
      calc
        -(28 * c0 ^ 2 + (1 / 250 : ℝ) * c2 ^ 2) ≤
            (2 / 3 : ℝ) * (c0 * c2) := hyoung
        _ ≤ C02 * c0 * c2 := by simpa only [mul_assoc] using hcompare
  have hcross04 :
      -(14 * c0 ^ 2 + (1 / 896 : ℝ) * c4 ^ 2) ≤
        C04 * c0 * c4 := by
    by_cases hp : 0 ≤ c0 * c4
    · have hnonneg : 0 ≤ C04 * (c0 * c4) :=
        mul_nonneg hC04 hp
      calc
        -(14 * c0 ^ 2 + (1 / 896 : ℝ) * c4 ^ 2) ≤ 0 := by
          nlinarith only [sq_nonneg c0, sq_nonneg c4]
        _ ≤ C04 * c0 * c4 := by simpa only [mul_assoc] using hnonneg
    · have hp' : c0 * c4 < 0 := lt_of_not_ge hp
      have hcompare : (1 / 4 : ℝ) * (c0 * c4) ≤
          C04 * (c0 * c4) :=
        mul_le_mul_of_nonpos_right hC04Upper hp'.le
      have hsquare := sq_nonneg (112 * c0 + c4)
      have hyoung :
          -(14 * c0 ^ 2 + (1 / 896 : ℝ) * c4 ^ 2) ≤
            (1 / 4 : ℝ) * (c0 * c4) := by
        nlinarith only [hsquare]
      calc
        -(14 * c0 ^ 2 + (1 / 896 : ℝ) * c4 ^ 2) ≤
            (1 / 4 : ℝ) * (c0 * c4) := hyoung
        _ ≤ C04 * c0 * c4 := by simpa only [mul_assoc] using hcompare
  have hcross24 :
      -((1329 / 10000 : ℝ) * c2 ^ 2 +
          (177 / 625 : ℝ) * c4 ^ 2) ≤
        C24 * c2 * c4 := by
    by_cases hp : 0 ≤ c2 * c4
    · have hnonneg : 0 ≤ C24 * (c2 * c4) :=
        mul_nonneg hC24 hp
      calc
        -((1329 / 10000 : ℝ) * c2 ^ 2 +
            (177 / 625 : ℝ) * c4 ^ 2) ≤ 0 := by
          nlinarith only [sq_nonneg c2, sq_nonneg c4]
        _ ≤ C24 * c2 * c4 := by simpa only [mul_assoc] using hnonneg
    · have hp' : c2 * c4 < 0 := lt_of_not_ge hp
      have hcompare : (19399 / 50000 : ℝ) * (c2 * c4) ≤
          C24 * (c2 * c4) :=
        mul_le_mul_of_nonpos_right hC24Upper hp'.le
      have hdisc : 0 ≤
          4 * (1329 / 10000 : ℝ) * (177 / 625 : ℝ) -
            (19399 / 50000 : ℝ) ^ 2 := by norm_num
      have hsquare := sq_nonneg
        (2 * (1329 / 10000 : ℝ) * c2 +
          (19399 / 50000 : ℝ) * c4)
      have hrest : 0 ≤
          (4 * (1329 / 10000 : ℝ) * (177 / 625 : ℝ) -
            (19399 / 50000 : ℝ) ^ 2) * c4 ^ 2 :=
        mul_nonneg hdisc (sq_nonneg c4)
      have hyoung :
          -((1329 / 10000 : ℝ) * c2 ^ 2 +
              (177 / 625 : ℝ) * c4 ^ 2) ≤
            (19399 / 50000 : ℝ) * (c2 * c4) := by
        nlinarith only [hsquare, hrest]
      calc
        -((1329 / 10000 : ℝ) * c2 ^ 2 +
            (177 / 625 : ℝ) * c4 ^ 2) ≤
            (19399 / 50000 : ℝ) * (c2 * c4) := hyoung
        _ ≤ C24 * c2 * c4 := by simpa only [mul_assoc] using hcompare
  have hp24 : (1 / 25 : ℝ) * N ≤
      A22 * c2 ^ 2 + A44 * c4 ^ 2 + C24 * c2 * c4 := by
    have h22 := mul_le_mul_of_nonneg_right hA22 (sq_nonneg c2)
    have h44 := mul_le_mul_of_nonneg_right hA44 (sq_nonneg c4)
    dsimp only [N]
    nlinarith
  have hconstant' : 3998 * c0 ^ 2 ≤ N := by
    dsimp only [N]
    nlinarith only [hconstant]
  have habsorb :
      (31 / 10 : ℝ) * c0 ^ 2 + 28 * c0 ^ 2 + 14 * c0 ^ 2 +
          (1 / 250 : ℝ) * c2 ^ 2 +
          (1 / 896 : ℝ) * c4 ^ 2 ≤
        (1 / 25 : ℝ) * N := by
    dsimp only [N] at hconstant' ⊢
    nlinarith only [hconstant', sq_nonneg c0, sq_nonneg c2, sq_nonneg c4]
  have hquadratic : 0 ≤
      A00 * c0 ^ 2 + A22 * c2 ^ 2 + A44 * c4 ^ 2 +
        C02 * c0 * c2 + C04 * c0 * c4 + C24 * c2 * c4 := by
    have h00 := mul_le_mul_of_nonneg_right hA00 (sq_nonneg c0)
    linear_combination h00 + hp24 + hcross02 + hcross04 + habsorb
  have hcore :=
    fourCellEvenZeroCoshCoupledCore_intrinsicEvenP024Profile_eq_quadratic
      c0 c2 c4
  have hmass := integral_factorTwoIntrinsicEvenP024Profile_sq c0 c2 c4
  rw [hmass, hcore]
  unfold symmetricQuadratic
  dsimp only [A00, A22, A44, C02, C04, C24, beta] at hquadratic
  nlinarith only [hquadratic]

private theorem upperStripPotential_le_fullPotential_of_even
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    2 * (∫ x : ℝ in 3 / 5..1,
        yoshidaEndpointPotential x * w x ^ 2) ≤
      ∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * w x ^ 2 := by
  let g : ℝ → ℝ := fun x ↦ yoshidaEndpointPotential x * w x ^ 2
  have hgFull : IntervalIntegrable g volume (-1) 1 := by
    simpa only [g] using intervalIntegrable_endpointPotential_mul_sq w hw
  have hgEven : Function.Even g := by
    intro x
    dsimp only [g, yoshidaEndpointPotential]
    rw [heven x]
    ring_nf
  have hfold := integral_neg_one_one_eq_two_mul_zero_one_of_even
    g hgFull hgEven
  have hleft : IntervalIntegrable g volume 0 (3 / 5) := by
    apply hgFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 3 / 5)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hright : IntervalIntegrable g volume (3 / 5) 1 := by
    apply hgFull.mono_set
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 / 5 : ℝ) ≤ 1)] at hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hleftNonneg : 0 ≤ ∫ x : ℝ in 0..3 / 5, g x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (yoshidaEndpointPotential_nonneg_on_Icc hxIcc)
      (sq_nonneg _)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hleft hright
  dsimp only [g] at hfold hsplit hleftNonneg ⊢
  linarith

/-- On an even profile, the exact endpoint potential pays the exact retained
dyadic translation while leaving a strict positive strip reserve. -/
theorem endpointPotential_sub_dyadicPairing_nonnegative
    (w : ℝ → ℝ) (hw : Continuous w) (heven : Function.Even w) :
    0 ≤ (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * w x ^ 2) -
      Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w := by
  let S : ℝ := ∫ x : ℝ in 3 / 5..1,
    yoshidaEndpointPotential x * w x ^ 2
  let V : ℝ := ∫ x : ℝ in -1..1,
    yoshidaEndpointPotential x * w x ^ 2
  let P : ℝ := Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w
  have hprime : P ≤ (99 / 50 : ℝ) * S := by
    simpa only [P, S] using
      fourCell_dyadicPairing_le_endpointStripPotential w hw heven
  have hstrip : 2 * S ≤ V := by
    simpa only [S, V] using
      upperStripPotential_le_fullPotential_of_even w hw heven
  have hS : 0 ≤ S := by
    dsimp only [S]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    have hxIcc : x ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (yoshidaEndpointPotential_nonneg_on_Icc hxIcc)
      (sq_nonneg _)
  change 0 ≤ V - P
  nlinarith

/-- The complete infinite even tail above `P₄` satisfies the actual
`33 / 20` coupled-core inequality.  The proof uses the sixth harmonic gap
for all higher modes at once and retains the prime/potential pair as the
exact positive endpoint-capacity block. -/
theorem thirtyThree_div_twenty_mass_le_coupledCore_of_even_legendreTail
    (w : ℝ → ℝ) (hw : Continuous w)
    (hlocal : LocallyLipschitzOn (Icc (-1 : ℝ) 1) w)
    (heven : Function.Even w)
    (hlow : centeredLegendreMomentsVanishBelow w 6) :
    (33 / 20 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
      fourCellEvenZeroCoshCoupledCore w := by
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let B : ℝ := (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * w x ^ 2) -
    Real.sqrt 2 * Real.log 2 * fourCellEndpointPairing w
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact intervalIntegral.integral_nonneg (by norm_num)
      (fun _ _ ↦ sq_nonneg _)
  have hB : 0 ≤ B := by
    simpa only [B] using
      endpointPotential_sub_dyadicPairing_nonnegative w hw heven
  have hraw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    w hw hlocal 6 hlow
  norm_num [harmonic, Finset.sum_range_succ] at hraw
  have hgap : (49 / 20 : ℝ) * M ≤ centeredRawLogEnergy w / 4 := by
    simpa only [M, factorTwoIntrinsicEnergy] using hraw
  unfold fourCellEvenZeroCoshCoupledCore
  dsimp only [M, B] at hgap hB ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaFourCellEvenZeroCoshCoupledCoreStructural
