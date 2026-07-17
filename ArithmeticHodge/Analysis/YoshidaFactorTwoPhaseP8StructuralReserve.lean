import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseEndpointTailMixedCauchyStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineStructural
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural

set_option autoImplicit false

open MeasureTheory Polynomial Real Set
open scoped BigOperators unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8StructuralReserve

open ShiftedLegendreBasis
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open YoshidaConstantBounds
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoEndpointBilinear
open YoshidaFactorTwoPhaseEndpointTailMixedCauchyStructural
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseHigherLegendreStructuralPositive
open YoshidaFactorTwoPhaseIntrinsicEvenLowKernelPositive
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineStructural
open YoshidaFactorTwoPhaseIntrinsicNineUnbalancedStaticDiskStructural
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive

noncomputable section

/-!
# A structural diagonal reserve for centered `P8`

When the odd profile vanishes, the alternating phase coordinate vanishes
identically.  Removing that unused coordinate from the projected remainder
estimate leaves a uniform `7/100` energy reserve at the cutoff-eight gap.
The proof is spectral and phase-uniform; it does not inspect phase samples.
-/

private theorem zero_locallyLipschitzOn :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) (0 : ℝ → ℝ) := by
  have hdiff : ContDiff ℝ 1 (fun _ : ℝ ↦ (0 : ℝ)) := contDiff_const
  change LocallyLipschitzOn (Icc (-1) 1) (fun _ : ℝ ↦ (0 : ℝ))
  exact hdiff.contDiffOn.locallyLipschitzOn (convex_Icc (-1) 1)

private theorem factorTwoEndpointChannelPhase_even_zero_b_independent
    (e : ℝ → ℝ) (a b : ℝ) :
    factorTwoEndpointChannelPhase e 0 a b =
      factorTwoEndpointChannelPhase e 0 a 0 := by
  have hAlt : factorTwoCenteredAlternatingCoupling e (0 : ℝ → ℝ) = 0 := by
    have h := factorTwoCenteredAlternatingCoupling_smul_right
      0 e (fun _ : ℝ ↦ 1)
    norm_num at h
    exact h
  unfold factorTwoEndpointChannelPhase
  rw [hAlt]
  ring

/-- The signed self-coordinate costs at most `17/24` when the alternating
coordinate is absent. -/
private theorem projected_self_phase_variable_le_seventeen_twenty_fourths
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    factorTwoIntrinsicSelfRegularHalfWidth * |a| +
        (Real.log 2 / Real.sqrt 2) * a ≤ 17 / 24 := by
  let d := factorTwoIntrinsicSelfRegularHalfWidth
  let alpha := Real.log 2 / Real.sqrt 2
  have hlogLower := six_hundred_ninety_three_div_thousand_lt_log_two
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  have hd0 : 0 ≤ d := by
    dsimp only [d]
    unfold factorTwoIntrinsicSelfRegularHalfWidth yoshidaEndpointA
    linarith
  have hdUpper : d < (43 / 200 : ℝ) := by
    dsimp only [d]
    unfold factorTwoIntrinsicSelfRegularHalfWidth yoshidaEndpointA
    linarith
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hsqrtUpper : Real.sqrt 2 < (3 / 2 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 2]
  have halphaUpper : alpha < (491 / 1000 : ℝ) := by
    dsimp only [alpha]
    rw [div_lt_iff₀ hsqrtPos]
    nlinarith [Real.log_two_lt_d9]
  have halphaLower : (4 / 9 : ℝ) < alpha := by
    dsimp only [alpha]
    rw [lt_div_iff₀ hsqrtPos]
    nlinarith
  have hdAlpha : d ≤ alpha := by linarith
  have hsum : d + alpha ≤ (17 / 24 : ℝ) := by linarith
  have habs : |a| ≤ 1 := by
    nlinarith [sq_abs a, abs_nonneg a]
  by_cases hapos : 0 ≤ a
  · rw [abs_of_nonneg hapos]
    have hscaled := mul_le_mul_of_nonneg_right hsum hapos
    have haone : a ≤ 1 := by nlinarith
    dsimp only [d, alpha] at hscaled ⊢
    nlinarith
  · have haneg : a < 0 := lt_of_not_ge hapos
    rw [abs_of_neg haneg]
    have hcancel : (alpha - d) * a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hdAlpha) haneg.le
    change d * -a + alpha * a ≤ 17 / 24
    rw [show d * -a + alpha * a = (alpha - d) * a by ring]
    norm_num at hcancel ⊢
    linarith

private theorem projectedEvenRemainderLoss_zero_add_seven_hundredths_le
    (a : ℝ) (ha : a ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedEvenRemainderLoss a 0 +
        Real.log 2 / 2 + (7 / 100 : ℝ) ≤
      (harmonic 8 : ℝ) + 1 / 10 := by
  have hphase :=
    projected_self_phase_variable_le_seventeen_twenty_fourths a ha
  have hbeta := log_three_div_sqrt_three_kernel_bounds.2
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hlog : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  have hlogSmall : Real.log 2 / 64 < (7 / 640 : ℝ) := by linarith
  unfold factorTwoIntrinsicProjectedEvenRemainderLoss
  norm_num [harmonic, Finset.sum_range_succ] at hphase ⊢
  linarith

/-- Every pure even cutoff-eight residual retains `7/100` of its intrinsic
energy, uniformly on the closed phase disk. -/
theorem seven_hundredths_energy_le_pure_even_cutoff_eight_phase
    (e : ℝ → ℝ) (hec : Continuous e) (he : Function.Even e)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (heLow : centeredLegendreMomentsVanishBelow e 8)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (7 / 100 : ℝ) * factorTwoIntrinsicEnergy e ≤
      factorTwoEndpointChannelPhase e 0 a b := by
  have ha : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg b]
  have hab0 : a ^ 2 + (0 : ℝ) ^ 2 ≤ 1 := by simpa using ha
  have heReserve :=
    harmonic_eight_add_one_tenth_mul_intrinsicEnergy_le_raw_add_half_potential
      e hec he helocal heLow
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    e (0 : ℝ → ℝ) hec (by fun_prop) helocal zero_locallyLipschitzOn
    a 0 hab0
  have hremainder := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    e (0 : ℝ → ℝ) hec (by fun_prop) he (by intro x; simp) he0
    a 0 hab0
  have hbudget :=
    projectedEvenRemainderLoss_zero_add_seven_hundredths_le a ha
  have henergy := factorTwoIntrinsicEnergy_nonneg e
  have hbudgetScaled := mul_le_mul_of_nonneg_right hbudget henergy
  have hzeroRaw : centeredRawLogEnergy (0 : ℝ → ℝ) = 0 := by
    unfold centeredRawLogEnergy
    simp
  have hzeroPotential :
      factorTwoIntrinsicPotentialEnergy (0 : ℝ → ℝ) = 0 := by
    unfold factorTwoIntrinsicPotentialEnergy
    simp
  have hzeroEnergy : factorTwoIntrinsicEnergy (0 : ℝ → ℝ) = 0 := by
    unfold factorTwoIntrinsicEnergy
    simp
  rw [hzeroRaw, hzeroPotential, hzeroEnergy] at hprotected
  rw [hzeroEnergy] at hremainder
  norm_num only [zero_div, add_zero, mul_zero, sub_zero] at hprotected hremainder
  have hphase :
      (7 / 100 : ℝ) * factorTwoIntrinsicEnergy e ≤
        factorTwoEndpointChannelPhase e 0 a 0 := by
    rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
      e (0 : ℝ → ℝ) hec (by fun_prop) a 0]
    nlinarith
  rw [factorTwoEndpointChannelPhase_even_zero_b_independent e a b]
  exact hphase

/-! ## Specialization to centered `P8` -/

theorem factorTwoCenteredP8_eq (x : ℝ) :
    factorTwoCenteredP8 x =
      (6435 * x ^ 8 - 12012 * x ^ 6 + 6930 * x ^ 4 -
        1260 * x ^ 2 + 35) / 128 := by
  unfold factorTwoCenteredP8 shiftedLegendreReal
  simp [Polynomial.shiftedLegendre, Finset.sum_range_succ, Nat.choose]
  ring

theorem continuous_factorTwoCenteredP8 : Continuous factorTwoCenteredP8 := by
  rw [show factorTwoCenteredP8 = fun x ↦
      (6435 * x ^ 8 - 12012 * x ^ 6 + 6930 * x ^ 4 -
        1260 * x ^ 2 + 35) / 128 by
    funext x
    exact factorTwoCenteredP8_eq x]
  fun_prop

theorem even_factorTwoCenteredP8 : Function.Even factorTwoCenteredP8 := by
  intro x
  rw [factorTwoCenteredP8_eq, factorTwoCenteredP8_eq]
  ring

theorem locallyLipschitzOn_factorTwoCenteredP8 :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) factorTwoCenteredP8 := by
  have h : ContDiff ℝ 1 factorTwoCenteredP8 := by
    rw [show factorTwoCenteredP8 = fun x ↦
        (6435 * x ^ 8 - 12012 * x ^ 6 + 6930 * x ^ 4 -
          1260 * x ^ 2 + 35) / 128 by
      funext x
      exact factorTwoCenteredP8_eq x]
    fun_prop
  exact h.locallyLipschitz.locallyLipschitzOn

theorem centeredPullback_factorTwoCenteredP8 (t : ℝ) :
    centeredPullback factorTwoCenteredP8 t =
      (shiftedLegendreReal 8).eval t := by
  unfold centeredPullback factorTwoCenteredP8
  congr 1
  ring

theorem factorTwoCenteredP8_momentsVanishBelow :
    centeredLegendreMomentsVanishBelow factorTwoCenteredP8 8 := by
  intro n hn
  rw [show (fun t : unitInterval ↦
      centeredPullback factorTwoCenteredP8 (t : ℝ) *
        (shiftedLegendreReal n).eval (t : ℝ)) =
      fun t : unitInterval ↦
        (shiftedLegendreReal 8).eval (t : ℝ) *
          (shiftedLegendreReal n).eval (t : ℝ) by
    funext t
    rw [centeredPullback_factorTwoCenteredP8]]
  change (∫ t : unitInterval,
    (fun x : ℝ ↦ (shiftedLegendreReal 8).eval x *
      (shiftedLegendreReal n).eval x) (t : ℝ)) = 0
  rw [integral_unitInterval_eq_intervalIntegral
    (fun x : ℝ ↦ (shiftedLegendreReal 8).eval x *
      (shiftedLegendreReal n).eval x)]
  exact integral_shiftedLegendreReal_mul_eq_zero (by omega)

theorem factorTwoCenteredP8_p0_zero :
    centeredEvenP0Coefficient factorTwoCenteredP8 = 0 := by
  exact centeredEvenP0Coefficient_eq_zero_of_momentsVanishBelow
    factorTwoCenteredP8 (by norm_num) factorTwoCenteredP8_momentsVanishBelow

theorem factorTwoCenteredP8_energy :
    factorTwoIntrinsicEnergy factorTwoCenteredP8 = 2 / 17 := by
  unfold factorTwoIntrinsicEnergy
  rw [show (fun x : ℝ ↦ factorTwoCenteredP8 x ^ 2) = fun x ↦
      ((6435 * x ^ 8 - 12012 * x ^ 6 + 6930 * x ^ 4 -
        1260 * x ^ 2 + 35) / 128) ^ 2 by
    funext x
    rw [factorTwoCenteredP8_eq]]
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [YoshidaEndpointOcticPotential.integral_pow_nat]
  norm_num

private theorem factorTwoIntrinsicEnergy_smul_real
    (c : ℝ) (w : ℝ → ℝ) :
    factorTwoIntrinsicEnergy (c • w) =
      c ^ 2 * factorTwoIntrinsicEnergy w := by
  unfold factorTwoIntrinsicEnergy
  rw [show (fun x : ℝ ↦ (c • w) x ^ 2) =
      fun x ↦ c ^ 2 * w x ^ 2 by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring,
    intervalIntegral.integral_const_mul]

/-- The centered `P8` line retains the explicit coefficient `7/850` after
arbitrary real scaling. -/
theorem seven_eight_hundred_fiftieths_sq_le_scaled_P8_phase
    (c a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    (7 / 850 : ℝ) * c ^ 2 ≤
      factorTwoEndpointChannelPhase (c • factorTwoCenteredP8) 0 a b := by
  have hbase := seven_hundredths_energy_le_pure_even_cutoff_eight_phase
    factorTwoCenteredP8 continuous_factorTwoCenteredP8 even_factorTwoCenteredP8
    factorTwoCenteredP8_p0_zero locallyLipschitzOn_factorTwoCenteredP8
    factorTwoCenteredP8_momentsVanishBelow a b hab
  have hscaled := mul_le_mul_of_nonneg_left hbase (sq_nonneg c)
  have hphaseScale := factorTwoEndpointChannelPhase_smul
    factorTwoCenteredP8 (0 : ℝ → ℝ) c a b
  simp only [smul_zero] at hphaseScale
  rw [factorTwoCenteredP8_energy] at hscaled
  rw [hphaseScale]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP8StructuralReserve
