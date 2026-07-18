import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCenteredP9Structural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineSemanticHandoffStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP7EndpointUpperStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP7P9CorrelationStructural
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialLegendreOffDiagonalStructural
import ArithmeticHodge.Analysis.YoshidaCoercivityNumerics

set_option autoImplicit false

open MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP7P9AllocationObstructionStructural

noncomputable section

open CenteredEndpointCorrelation
open UnitIntervalLogEnergyAffine
open ShiftedLegendreBasis
open ShiftedLegendreCenteredLowModes
open ShiftedLegendreLogEnergyOrthogonalProjection
open ShiftedLegendreOrthogonality
open YoshidaCoercivityNumerics
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialLegendreOffDiagonalStructural
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoCenteredPhysical
open YoshidaFactorTwoPhaseEnvelope
open YoshidaFactorTwoPhaseCenteredP9Structural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicNineComplementSchurStructural
open YoshidaFactorTwoPhaseIntrinsicNineEnhancedTailReserveStructural
open YoshidaFactorTwoPhaseIntrinsicNineFullMixedDecompositionStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseIntrinsicSixSchurReduction
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseLowSchur
open YoshidaFactorTwoPhaseP7EndpointUpperStructural
open YoshidaFactorTwoPhaseP7P9CorrelationStructural
open YoshidaFactorTwoPhaseP67ResidualAnalyticSchurStructural
open YoshidaFactorTwoPhaseP67ResidualRegularDecompositionStructural
open YoshidaFactorTwoPhaseP678CombinedResidualSchurStructural
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRegularKernelSchur
open YoshidaRegularKernelSharpMeanZeroSchur

/-!
# The `P7/P9` obstruction to the cutoff-nine survivor allocation

The honest low--tail determinant is not replaced here.  We isolate the
strictly stronger determinant demanded by the enhanced survivor allocation
and prove that this allocation cannot hold on the structural Legendre pair
`(P7,P9)` at phase `(1,0)`.
-/

/-- Complete low--tail half-cross for the retained `P7` and omitted `P9`. -/
def factorTwoP7P9Mixed : ℝ :=
  factorTwoEndpointLowTailMixed
    0 0 factorTwoCenteredP7 factorTwoCenteredP9 1 0

/-- The forward row already charged to the retained `P678` reserve. -/
def factorTwoP7P9Forward : ℝ :=
  factorTwoP678ResidualCombinedForwardMixed
    0 factorTwoCenteredP9 0 1 0 1 0

/-- The scalar determinant demanded by the enhanced survivor handoff. -/
def factorTwoP7P9AllocatedDeterminant : ℝ :=
  (factorTwoP7PhaseDiagonal 1 - 1 / 800) *
      factorTwoIntrinsicNineSurvivorResidualReserve 0 factorTwoCenteredP9 -
    15 * (factorTwoP7P9Mixed - factorTwoP7P9Forward) ^ 2

private theorem factorTwoP9SurvivorReserve_eq :
    factorTwoIntrinsicNineSurvivorResidualReserve 0 factorTwoCenteredP9 =
      1 / 23750 + (1 / 2 : ℝ) *
        factorTwoIntrinsicPotentialEnergy factorTwoCenteredP9 := by
  have hzeroEnergy : factorTwoIntrinsicEnergy (0 : ℝ → ℝ) = 0 := by
    simp [factorTwoIntrinsicEnergy]
  have hzeroPotential :
      factorTwoIntrinsicPotentialEnergy (0 : ℝ → ℝ) = 0 := by
    simp [factorTwoIntrinsicPotentialEnergy]
  unfold factorTwoIntrinsicNineSurvivorResidualReserve
  rw [hzeroEnergy, hzeroPotential, factorTwoCenteredP9_energy]
  ring

private theorem factorTwoIntrinsicNineEvenProfile_zero :
    factorTwoIntrinsicNineEvenProfile 0 0 0 0 0 = 0 := by
  funext x
  simp [factorTwoIntrinsicNineEvenProfile,
    YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural.factorTwoIntrinsicEightEvenProfile,
    factorTwoEvenStructuralLowProfile, factorTwoIntrinsicSixEvenTail]

private theorem factorTwoIntrinsicNineOddProfile_P7 :
    factorTwoIntrinsicNineOddProfile 0 0 0 1 = factorTwoCenteredP7 := by
  funext x
  simp [factorTwoIntrinsicNineOddProfile,
    YoshidaFactorTwoPhaseIntrinsicEightUnbalancedStaticDiskStructural.factorTwoIntrinsicEightOddProfile,
    factorTwoIntrinsicSixOddTail,
    YoshidaEndpointOddResidualRegularity.factorTwoOddStructuralLowProfile]

/-- On the witness, subtracting the certified forward row leaves precisely
the five-family nonpolynomial survivor. -/
theorem factorTwoP7P9Remaining_eq_nonpolynomial :
    factorTwoP7P9Mixed - factorTwoP7P9Forward =
      factorTwoIntrinsicNineNonpolynomialMixed
        0 factorTwoCenteredP7 0 factorTwoCenteredP9 1 0 := by
  have hzeroGap :
      centeredLegendreMomentsVanishBelow (0 : ℝ → ℝ) 9 := by
    intro n hn
    simp [centeredPullback]
  have hzeroLocal :
      LocallyLipschitzOn (Icc (-1 : ℝ) 1) (0 : ℝ → ℝ) := by
    have hdiff : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
    exact hdiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)
  have hmix := factorTwoEndpointLowTailMixed_intrinsicNine_eq
    (0 : ℝ → ℝ) factorTwoCenteredP9 continuous_zero
    continuous_factorTwoCenteredP9 hzeroLocal
    locallyLipschitzOn_factorTwoCenteredP9 odd_factorTwoCenteredP9
    hzeroGap factorTwoCenteredP9_momentsVanishBelow
    0 0 0 0 0 0 0 0 1 1 0
  rw [factorTwoIntrinsicNineEvenProfile_zero,
    factorTwoIntrinsicNineOddProfile_P7] at hmix
  unfold factorTwoP7P9Mixed factorTwoP7P9Forward
  simp [factorTwoEvenStructuralLowProfile, factorTwoIntrinsicSixEvenTail,
    factorTwoIntrinsicSixOddTail,
    YoshidaEndpointOddResidualRegularity.factorTwoOddStructuralLowProfile,
    factorTwoP67ResidualSmoothMixedIntegrand,
    factorTwoP67ResidualSymmetricCrossSum,
    factorTwoP67ResidualAlternatingCrossSum,
    factorTwoP67ResidualAlternatingCrossDifference,
    factorTwoCenteredCorrelationBilinear,
    factorTwoCenteredCrossCorrelation] at hmix
  linarith

private theorem factorTwoCenteredP7_eq_neg_centeredLegendre :
    factorTwoCenteredP7 =
      fun x ↦ -(centeredShiftedLegendreReal 7).eval x := by
  funext x
  rw [eval_centeredShiftedLegendreReal]
  rfl

private theorem factorTwoCenteredP9_eq_neg_centeredLegendre :
    factorTwoCenteredP9 =
      fun x ↦ -(centeredShiftedLegendreReal 9).eval x := by
  funext x
  rw [eval_centeredShiftedLegendreReal]
  rfl

/-- The endpoint-potential cross is the inverse Legendre spectral gap. -/
theorem integral_endpointPotential_mul_P7_mul_P9 :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointPotential x * factorTwoCenteredP7 x *
        factorTwoCenteredP9 x) = 1 / 17 := by
  have h := integral_endpointPotential_mul_centeredShiftedLegendreReal_of_even
    (m := 7) (n := 9) (by norm_num) (by norm_num)
  rw [factorTwoCenteredP7_eq_neg_centeredLegendre,
    factorTwoCenteredP9_eq_neg_centeredLegendre]
  norm_num at h ⊢
  simpa only [mul_neg, neg_mul, neg_neg] using h

private theorem factorTwoCenteredP7_eq_centeredPolynomialLift :
    factorTwoCenteredP7 =
      centeredPolynomialLift (-(shiftedLegendreReal 7)) := by
  funext x
  simp [centeredPolynomialLift, factorTwoCenteredP7]

/-- Orthogonality of the retained and omitted odd Legendre modes. -/
theorem integral_factorTwoCenteredP7_mul_P9_eq_zero :
    (∫ x : ℝ in -1..1,
      factorTwoCenteredP7 x * factorTwoCenteredP9 x) = 0 := by
  have hdeg :
      (-(shiftedLegendreReal 7)).natDegree < 9 := by
    simp [natDegree_shiftedLegendreReal]
  have h := intervalIntegral_centeredPolynomialLift_mul_tail_eq_zero
    (-(shiftedLegendreReal 7)) factorTwoCenteredP9
    continuous_factorTwoCenteredP9 factorTwoCenteredP9_momentsVanishBelow hdeg
  rwa [← factorTwoCenteredP7_eq_centeredPolynomialLift] at h

/-- The `P7+P9` energy is the sum of the two Legendre masses. -/
theorem factorTwoIntrinsicEnergy_P7_add_P9 :
    factorTwoIntrinsicEnergy (factorTwoCenteredP7 + factorTwoCenteredP9) =
      68 / 285 := by
  have h7 : IntervalIntegrable (fun x : ℝ ↦ factorTwoCenteredP7 x ^ 2)
      volume (-1) 1 := continuous_factorTwoCenteredP7.pow 2 |>.intervalIntegrable _ _
  have h79 : IntervalIntegrable
      (fun x : ℝ ↦ 2 * (factorTwoCenteredP7 x * factorTwoCenteredP9 x))
      volume (-1) 1 :=
    ((continuous_factorTwoCenteredP7.mul continuous_factorTwoCenteredP9).const_mul 2)
      |>.intervalIntegrable _ _
  have h9 : IntervalIntegrable (fun x : ℝ ↦ factorTwoCenteredP9 x ^ 2)
      volume (-1) 1 := continuous_factorTwoCenteredP9.pow 2 |>.intervalIntegrable _ _
  unfold factorTwoIntrinsicEnergy
  rw [show (fun x : ℝ ↦
      (factorTwoCenteredP7 + factorTwoCenteredP9) x ^ 2) =
      fun x ↦ factorTwoCenteredP7 x ^ 2 +
        (2 * (factorTwoCenteredP7 x * factorTwoCenteredP9 x) +
          factorTwoCenteredP9 x ^ 2) by
    funext x
    simp only [Pi.add_apply]
    ring,
    intervalIntegral.integral_add h7 (h79.add h9),
    intervalIntegral.integral_add h79 h9,
    intervalIntegral.integral_const_mul,
    integral_factorTwoCenteredP7_mul_P9_eq_zero]
  change factorTwoIntrinsicEnergy factorTwoCenteredP7 +
      (2 * 0 + factorTwoIntrinsicEnergy factorTwoCenteredP9) = 68 / 285
  rw [factorTwoCenteredP7_energy, factorTwoCenteredP9_energy]
  norm_num

private theorem abs_re_regularQuadratic_le_of_mean_zero
    (w : ℝ → ℝ) (hw : Continuous w)
    (hmean : (∫ x : ℝ in -1..1, w x) = 0) :
    |(yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re| ≤
      (1 / 32 : ℝ) * factorTwoIntrinsicEnergy w := by
  let f : ℝ → ℂ := fun x ↦ (w x : ℂ)
  have hf : Continuous f := by
    dsimp only [f]
    fun_prop
  have hmeanInterval : (∫ x : ℝ in -1..1, f x) = 0 := by
    change (∫ x : ℝ in -1..1, (w x : ℂ)) = (0 : ℂ)
    rw [intervalIntegral.integral_ofReal, hmean]
    norm_num
  have hmeanSet : (∫ x : ℝ in Icc (-1) 1, f x) = 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hmeanInterval
  have hmass :
      (∫ x : ℝ in Icc (-1) 1, ‖f x‖ ^ 2) =
        factorTwoIntrinsicEnergy w := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    unfold factorTwoIntrinsicEnergy
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp only [f]
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnorm :=
    norm_yoshidaEndpointRegularQuadratic_le_one_thirty_second_of_integral_eq_zero
      f hf hmeanSet
  rw [hmass] at hnorm
  exact (Complex.abs_re_le_norm _).trans hnorm

/-- The regular-kernel polarization loss is tiny on the orthogonal odd pair. -/
theorem factorTwoP7P9_regular_mixed_gt_neg_three_over_140 :
    -(3 / 140 : ℝ) <
      -(yoshidaEndpointA / 2) *
        ((yoshidaEndpointRegularQuadratic
              (fun x ↦ ((factorTwoCenteredP7 + factorTwoCenteredP9) x : ℂ))).re -
          (yoshidaEndpointRegularQuadratic
              (fun x ↦ (factorTwoCenteredP7 x : ℂ))).re -
          (yoshidaEndpointRegularQuadratic
              (fun x ↦ (factorTwoCenteredP9 x : ℂ))).re) := by
  have hoddAdd : Function.Odd
      (factorTwoCenteredP7 + factorTwoCenteredP9) :=
    odd_factorTwoCenteredP7.add odd_factorTwoCenteredP9
  have hmeanAdd := centered_interval_integral_eq_zero_of_odd
    (factorTwoCenteredP7 + factorTwoCenteredP9) hoddAdd
  have hmean7 := centered_interval_integral_eq_zero_of_odd
    factorTwoCenteredP7 odd_factorTwoCenteredP7
  have hmean9 := centered_interval_integral_eq_zero_of_odd
    factorTwoCenteredP9 odd_factorTwoCenteredP9
  have hAdd := abs_re_regularQuadratic_le_of_mean_zero
    (factorTwoCenteredP7 + factorTwoCenteredP9)
    (continuous_factorTwoCenteredP7.add continuous_factorTwoCenteredP9) hmeanAdd
  have h7 := abs_re_regularQuadratic_le_of_mean_zero
    factorTwoCenteredP7 continuous_factorTwoCenteredP7 hmean7
  have h9 := abs_re_regularQuadratic_le_of_mean_zero
    factorTwoCenteredP9 continuous_factorTwoCenteredP9 hmean9
  rw [factorTwoIntrinsicEnergy_P7_add_P9] at hAdd
  rw [factorTwoCenteredP7_energy] at h7
  rw [factorTwoCenteredP9_energy] at h9
  let cross : ℝ :=
    (yoshidaEndpointRegularQuadratic
          (fun x ↦ ((factorTwoCenteredP7 + factorTwoCenteredP9) x : ℂ))).re -
      (yoshidaEndpointRegularQuadratic
          (fun x ↦ (factorTwoCenteredP7 x : ℂ))).re -
      (yoshidaEndpointRegularQuadratic
          (fun x ↦ (factorTwoCenteredP9 x : ℂ))).re
  have hcross : cross ≤ 17 / 1140 := by
    dsimp only [cross]
    have hAddUpper := (le_abs_self _).trans hAdd
    have h7Lower := (neg_le_abs _).trans h7
    have h9Lower := (neg_le_abs _).trans h9
    norm_num at hAddUpper h7Lower h9Lower ⊢
    linarith
  have hscale : 0 ≤ yoshidaEndpointA / 2 :=
    div_nonneg yoshidaEndpointA_pos.le (by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hcross hscale
  have hlog : Real.log 2 < (7 / 10 : ℝ) :=
    Real.log_two_lt_d9.trans (by norm_num)
  have hsmall :
      (yoshidaEndpointA / 2) * (17 / 1140 : ℝ) < 3 / 140 := by
    unfold yoshidaEndpointA
    nlinarith
  dsimp only [cross] at hscaled
  nlinarith

private theorem yoshidaEndpointCoshMoment_eq_centeredCoshMoment
    (w : ℝ → ℝ) :
    yoshidaEndpointCoshMoment w =
      centeredCoshMoment w (yoshidaEndpointA / 2) := by
  unfold centeredCoshMoment yoshidaEndpointCoshMoment
  apply intervalIntegral.integral_congr
  intro x _hx
  ring_nf

private theorem factorTwoCenteredP9_hyperbolic_nonpos :
    yoshidaEndpointHyperbolicQuadratic
        (fun x ↦ (factorTwoCenteredP9 x : ℂ)) ≤ 0 := by
  have hcosh : yoshidaEndpointCoshMoment factorTwoCenteredP9 = 0 := by
    rw [yoshidaEndpointCoshMoment_eq_centeredCoshMoment]
    exact centeredCoshMoment_eq_zero_of_odd odd_factorTwoCenteredP9
      (yoshidaEndpointA / 2)
  rw [yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments, hcosh]
  have hA := yoshidaEndpointA_pos
  nlinarith [sq_nonneg (yoshidaEndpointSinhMoment factorTwoCenteredP9)]

/-- The rank-two hyperbolic polarization costs less than `1/500`. -/
theorem factorTwoP7P9_hyperbolic_mixed_gt_neg_one_over_500 :
    -(1 / 500 : ℝ) <
      (1 / 2 : ℝ) *
        (yoshidaEndpointHyperbolicQuadratic
              (fun x ↦ ((factorTwoCenteredP7 + factorTwoCenteredP9) x : ℂ)) -
          yoshidaEndpointHyperbolicQuadratic
              (fun x ↦ (factorTwoCenteredP7 x : ℂ)) -
          yoshidaEndpointHyperbolicQuadratic
              (fun x ↦ (factorTwoCenteredP9 x : ℂ))) := by
  have hAddContinuous : Continuous
      (fun x ↦ ((factorTwoCenteredP7 + factorTwoCenteredP9) x : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_factorTwoCenteredP7.add continuous_factorTwoCenteredP9)
  have hAdd := yoshidaEndpointHyperbolicQuadratic_lower
    (fun x ↦ ((factorTwoCenteredP7 + factorTwoCenteredP9) x : ℂ))
    hAddContinuous
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hAdd
  change -(1 / Real.sqrt 2 - Real.log 2) *
      factorTwoIntrinsicEnergy (factorTwoCenteredP7 + factorTwoCenteredP9) ≤
    yoshidaEndpointHyperbolicQuadratic
      (fun x ↦ ((factorTwoCenteredP7 + factorTwoCenteredP9) x : ℂ)) at hAdd
  rw [factorTwoIntrinsicEnergy_P7_add_P9] at hAdd
  have h7 := factorTwoCenteredP7_hyperbolic_nonpos
  have h9 := factorTwoCenteredP9_hyperbolic_nonpos
  have hsqrt := inv_sqrt_two_lt_177_div_250
  have hlog := log_two_gt_693_div_1000
  nlinarith

private theorem factorTwoP7P9_phaseCorrelation_cross (t : ℝ) :
    factorTwoCenteredPhaseCorrelation
          0 (factorTwoCenteredP7 + factorTwoCenteredP9) 1 0 t -
        factorTwoCenteredPhaseCorrelation 0 factorTwoCenteredP7 1 0 t -
        factorTwoCenteredPhaseCorrelation 0 factorTwoCenteredP9 1 0 t =
      2 * factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 t := by
  unfold factorTwoCenteredPhaseCorrelation
  rw [centeredEndpointCorrelation_add
    factorTwoCenteredP7 factorTwoCenteredP9
    continuous_factorTwoCenteredP7 continuous_factorTwoCenteredP9 t]
  simp [centeredEndpointCorrelation]
  ring

private theorem factorTwoP7P9_reflected_integrals_cross :
    (∫ t : ℝ in 0..2,
        factorTwoCenteredPhaseCorrelation
          0 (factorTwoCenteredP7 + factorTwoCenteredP9) 1 0 t / (2 - t)) -
      (∫ t : ℝ in 0..2,
        factorTwoCenteredPhaseCorrelation
          0 factorTwoCenteredP7 1 0 t / (2 - t)) -
      (∫ t : ℝ in 0..2,
        factorTwoCenteredPhaseCorrelation
          0 factorTwoCenteredP9 1 0 t / (2 - t)) =
    2 * (∫ t : ℝ in 0..2,
      factorTwoCenteredCorrelationBilinear
        factorTwoCenteredP7 factorTwoCenteredP9 t / (2 - t)) := by
  have hFull := intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
    0 (factorTwoCenteredP7 + factorTwoCenteredP9) continuous_zero
    (continuous_factorTwoCenteredP7.add continuous_factorTwoCenteredP9) 1 0
  have h7 := intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
    0 factorTwoCenteredP7 continuous_zero continuous_factorTwoCenteredP7 1 0
  have h9 := intervalIntegrable_factorTwoCenteredPhaseCorrelation_div_two_sub
    0 factorTwoCenteredP9 continuous_zero continuous_factorTwoCenteredP9 1 0
  rw [← intervalIntegral.integral_sub hFull h7,
    ← intervalIntegral.integral_sub (hFull.sub h7) h9,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  rw [show
      factorTwoCenteredPhaseCorrelation
            0 (factorTwoCenteredP7 + factorTwoCenteredP9) 1 0 t / (2 - t) -
          factorTwoCenteredPhaseCorrelation 0 factorTwoCenteredP7 1 0 t /
              (2 - t) -
          factorTwoCenteredPhaseCorrelation 0 factorTwoCenteredP9 1 0 t /
              (2 - t) =
        (factorTwoCenteredPhaseCorrelation
              0 (factorTwoCenteredP7 + factorTwoCenteredP9) 1 0 t -
            factorTwoCenteredPhaseCorrelation 0 factorTwoCenteredP7 1 0 t -
            factorTwoCenteredPhaseCorrelation 0 factorTwoCenteredP9 1 0 t) /
          (2 - t) by ring,
    factorTwoP7P9_phaseCorrelation_cross]
  ring

/-- Exact five-family form of the surviving mixed row. -/
theorem factorTwoP7P9_nonpolynomial_eq_five_families :
    factorTwoIntrinsicNineNonpolynomialMixed
        0 factorTwoCenteredP7 0 factorTwoCenteredP9 1 0 =
      (∫ x : ℝ in -1..1,
        yoshidaEndpointPotential x * factorTwoCenteredP7 x *
          factorTwoCenteredP9 x) -
      (1 / 2 : ℝ) * (∫ t : ℝ in 0..2,
        factorTwoCenteredCorrelationBilinear
          factorTwoCenteredP7 factorTwoCenteredP9 t / (2 - t)) -
      (yoshidaEndpointA / 2) *
        ((yoshidaEndpointRegularQuadratic
              (fun x ↦ ((factorTwoCenteredP7 + factorTwoCenteredP9) x : ℂ))).re -
          (yoshidaEndpointRegularQuadratic
              (fun x ↦ (factorTwoCenteredP7 x : ℂ))).re -
          (yoshidaEndpointRegularQuadratic
              (fun x ↦ (factorTwoCenteredP9 x : ℂ))).re) +
      (1 / 2 : ℝ) *
        (yoshidaEndpointHyperbolicQuadratic
              (fun x ↦ ((factorTwoCenteredP7 + factorTwoCenteredP9) x : ℂ)) -
          yoshidaEndpointHyperbolicQuadratic
              (fun x ↦ (factorTwoCenteredP7 x : ℂ)) -
          yoshidaEndpointHyperbolicQuadratic
              (fun x ↦ (factorTwoCenteredP9 x : ℂ))) -
      (Real.log 3 / Real.sqrt 3) *
        factorTwoCenteredCorrelationBilinear
          factorTwoCenteredP7 factorTwoCenteredP9
          (factorTwoPrimeShift / yoshidaEndpointA) := by
  unfold factorTwoIntrinsicNineNonpolynomialMixed
  simp only [zero_add, neg_zero]
  rw [factorTwoP7P9_reflected_integrals_cross]
  have hprime := factorTwoP7P9_phaseCorrelation_cross
    (factorTwoPrimeShift / yoshidaEndpointA)
  rw [hprime]
  simp [yoshidaEndpointRegularQuadratic,
    yoshidaEndpointHyperbolicQuadratic]
  ring

/-- The complete surviving `P7/P9` row is strictly larger than `1/24`.

This is the structural assembly point: the endpoint potential and reflected
families give the positive reserve, the sharp mean-zero regular and
hyperbolic estimates bound the two analytic losses, and the retained prime
atom has the favorable sign. -/
theorem factorTwoP7P9Remaining_gt_one_div_24 :
    (1 / 24 : ℝ) < factorTwoP7P9Mixed - factorTwoP7P9Forward := by
  rw [factorTwoP7P9Remaining_eq_nonpolynomial,
    factorTwoP7P9_nonpolynomial_eq_five_families,
    integral_endpointPotential_mul_P7_mul_P9]
  have hreflected :
      (1 / 150 : ℝ) < -(1 / 2 : ℝ) *
        (∫ t : ℝ in 0..2,
          factorTwoCenteredCorrelationBilinear
            factorTwoCenteredP7 factorTwoCenteredP9 t / (2 - t)) := by
    rw [integral_factorTwoCenteredCorrelationBilinear_P7_P9_div_two_sub]
    norm_num
  have hregular := factorTwoP7P9_regular_mixed_gt_neg_three_over_140
  have hhyperbolic := factorTwoP7P9_hyperbolic_mixed_gt_neg_one_over_500
  have hprime := factorTwoP7P9_prime_mixed_contribution_nonnegative
  linarith

/- The principal analytic input is deliberately exposed: proving this lower
bound rules out the allocation without claiming that the honest phase form
is negative. -/
theorem factorTwoP7P9AllocatedDeterminant_lt_neg_one_div_960_of_remaining
    (hremaining : 1 / 24 < factorTwoP7P9Mixed - factorTwoP7P9Forward) :
    factorTwoP7P9AllocatedDeterminant < -(1 / 960) := by
  have hLow : factorTwoP7PhaseDiagonal 1 - 1 / 800 < 2 / 3 := by
    linarith [factorTwoP7PhaseDiagonal_one_lt_two_thirds]
  have hTail :
      factorTwoIntrinsicNineSurvivorResidualReserve
          0 factorTwoCenteredP9 < 3 / 80 := by
    rw [factorTwoP9SurvivorReserve_eq]
    exact factorTwoCenteredP9_survivor_reserve_lt_three_fortieths
  have hTailNonneg :
      0 ≤ factorTwoIntrinsicNineSurvivorResidualReserve
        0 factorTwoCenteredP9 :=
    factorTwoIntrinsicNineSurvivorResidualReserve_nonneg _ _
  unfold factorTwoP7P9AllocatedDeterminant
  by_cases hLowNonneg : 0 ≤ factorTwoP7PhaseDiagonal 1 - 1 / 800
  · have hproduct :
        (factorTwoP7PhaseDiagonal 1 - 1 / 800) *
            factorTwoIntrinsicNineSurvivorResidualReserve
              0 factorTwoCenteredP9 < (2 / 3) * (3 / 80) := by
      exact (mul_le_mul_of_nonneg_right hLow.le hTailNonneg).trans_lt
        (mul_lt_mul_of_pos_left hTail (by norm_num))
    nlinarith [sq_nonneg
      ((factorTwoP7P9Mixed - factorTwoP7P9Forward) - 1 / 24)]
  · have hLowNeg : factorTwoP7PhaseDiagonal 1 - 1 / 800 < 0 :=
      lt_of_not_ge hLowNonneg
    have hproductNonpos :
        (factorTwoP7PhaseDiagonal 1 - 1 / 800) *
            factorTwoIntrinsicNineSurvivorResidualReserve
              0 factorTwoCenteredP9 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hLowNeg.le hTailNonneg
    nlinarith [sq_nonneg
      ((factorTwoP7P9Mixed - factorTwoP7P9Forward) - 1 / 24)]

/-- The cutoff-nine enhanced survivor allocation is impossible on the
structural `(P7,P9)` witness.  This concerns the allocated determinant only;
it makes no claim that the honest low--tail determinant is negative. -/
theorem factorTwoP7P9AllocatedDeterminant_lt_neg_one_div_960 :
    factorTwoP7P9AllocatedDeterminant < -(1 / 960) :=
  factorTwoP7P9AllocatedDeterminant_lt_neg_one_div_960_of_remaining
    factorTwoP7P9Remaining_gt_one_div_24

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineP7P9AllocationObstructionStructural
