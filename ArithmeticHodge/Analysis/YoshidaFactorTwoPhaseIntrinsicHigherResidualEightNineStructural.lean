import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
import ArithmeticHodge.Analysis.YoshidaConstantBounds

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set
open scoped BigOperators InnerProductSpace unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineStructural

open ShiftedLegendreCenteredParity
open ShiftedLegendreFiniteEnergyGap
open ShiftedLegendreL2Basis
open ShiftedLegendreL2HigherGap
open ShiftedLegendreL2SpectralGap
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaConstantBounds
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointPullbackLipschitz
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual
open TwoByTwoSchur

noncomputable section

/-! # Structural cutoff-eight/cutoff-nine higher residual -/

/-- Keeping the exact alternating coefficient `203 / 640` in the disk
Cauchy estimate improves the phase-variable bound enough to remove the odd
degree-nine mode. -/
theorem projected_phase_variable_le_777_div_1000
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicSelfRegularHalfWidth * |a| +
        (203 / 640 : ℝ) * |b| +
        (Real.log 2 / Real.sqrt 2) * a ≤
      777 / 1000 := by
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
  have halphaUpper : alpha < (491 / 1000 : ℝ) := by
    have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsqrtLower : (707 / 500 : ℝ) < Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2]
    have hlog := Real.log_two_lt_d9
    dsimp only [alpha]
    rw [div_lt_iff₀ hsqrtPos]
    nlinarith
  have halphaLower : (4 / 9 : ℝ) < alpha := by
    have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsqrtUpper : Real.sqrt 2 < (3 / 2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 2]
    dsimp only [alpha]
    rw [lt_div_iff₀ hsqrtPos]
    nlinarith
  have hdAlpha : d ≤ alpha := by linarith
  have hsum : d + alpha ≤ (17 / 24 : ℝ) := by linarith
  have hbSq : |b| ^ 2 = b ^ 2 := sq_abs b
  have hbDisk : a ^ 2 + |b| ^ 2 ≤ 1 := by simpa only [hbSq] using hab
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha]
    have hlinear :
        (d + alpha) * a + (203 / 640 : ℝ) * |b| ≤
          (17 / 24 : ℝ) * a + (203 / 640 : ℝ) * |b| := by
      nlinarith [mul_le_mul_of_nonneg_right hsum ha]
    have hcauchy := sq_nonneg ((203 / 640 : ℝ) * a -
      (17 / 24 : ℝ) * |b|)
    have htarget :
        (17 / 24 : ℝ) * a + (203 / 640 : ℝ) * |b| ≤
          777 / 1000 := by
      nlinarith [abs_nonneg b]
    dsimp only [d, alpha] at hlinear ⊢
    nlinarith
  · have haNeg : a < 0 := lt_of_not_ge ha
    rw [abs_of_neg haNeg]
    have hcancel : (alpha - d) * a ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hdAlpha) haNeg.le
    have hbOne : |b| ≤ 1 := by nlinarith [abs_nonneg b]
    change d * -a + (203 / 640 : ℝ) * |b| + alpha * a ≤ 777 / 1000
    rw [show d * -a + (203 / 640 : ℝ) * |b| + alpha * a =
        (alpha - d) * a + (203 / 640 : ℝ) * |b| by ring]
    nlinarith

/-- The complete even projected loss after the sharpened disk estimate. -/
theorem projectedEvenRemainderLoss_lt_4926971_div_2000000
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedEvenRemainderLoss a b <
      (4926971 / 2000000 : ℝ) := by
  have hphase := projected_phase_variable_le_777_div_1000 a b hab
  have hbeta : Real.log 3 / Real.sqrt 3 < (16 / 25 : ℝ) := by
    have hsqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    have hsqrtSq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsqrtLower : (173 / 100 : ℝ) < Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3]
    have hpow : (3 : ℝ) ^ 17 < (2 : ℝ) ^ 27 := by norm_num
    have hlog := Real.strictMonoOn_log (by norm_num) (by norm_num) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    have hlogUpper := Real.log_two_lt_d9
    rw [div_lt_iff₀ hsqrtPos]
    norm_num at hlog
    nlinarith
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hlog : Real.log 2 / 64 < (7 / 640 : ℝ) := by
    have := Real.log_two_lt_d9
    linarith
  unfold factorTwoIntrinsicProjectedEvenRemainderLoss
  norm_num at hphase ⊢
  linarith

/-- The odd loss fits the ninth harmonic gap once the exact alternating
coefficient is retained in the disk estimate. -/
theorem projectedOddRemainderLoss_le_harmonic_nine
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedOddRemainderLoss a b ≤
      (harmonic 9 : ℝ) - Real.log 2 / 2 := by
  have heven := projectedEvenRemainderLoss_lt_4926971_div_2000000 a b hab
  have hsqrt := inv_sqrt_two_lt_one_hundred_seventy_seven_div_two_hundred_fifty
  have hsqrt' : (Real.sqrt 2)⁻¹ < (177 / 250 : ℝ) := by
    simpa only [one_div] using hsqrt
  have hlogLower := six_hundred_ninety_three_div_thousand_lt_log_two
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  unfold factorTwoIntrinsicProjectedOddRemainderLoss
  norm_num [harmonic, Finset.sum_range_succ] at heven ⊢
  linarith

/-- Complete phase positivity above the ninth gap in both parity channels.
This already removes the retained odd degree-nine mode from the canonical
low block. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_nine_nine_higher_residual
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heLow : centeredLegendreMomentsVanishBelow e 9)
    (hoLow : centeredLegendreMomentsVanishBelow o 9)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have heRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    e hec helocal 9 heLow
  have hoRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    o hoc holocal 9 hoLow
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    e o hec hoc helocal holocal a b hab
  have heLoss := projectedEvenRemainderLoss_le_harmonic_nine a b hab
  have hoLoss := projectedOddRemainderLoss_le_harmonic_nine a b hab
  have hremainder := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    e o hec hoc he ho he0 a b hab
  have heEnergy := factorTwoIntrinsicEnergy_nonneg e
  have hoEnergy := factorTwoIntrinsicEnergy_nonneg o
  have heLossScaled := mul_le_mul_of_nonneg_right heLoss heEnergy
  have hoLossScaled := mul_le_mul_of_nonneg_right hoLoss hoEnergy
  have hpotential : 0 ≤ (1 / 2 : ℝ) *
      (factorTwoIntrinsicPotentialEnergy e +
        factorTwoIntrinsicPotentialEnergy o) := by
    exact mul_nonneg (by norm_num)
      (add_nonneg (factorTwoIntrinsicPotentialEnergy_nonneg e)
        (factorTwoIntrinsicPotentialEnergy_nonneg o))
  rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    e o hec hoc a b]
  nlinarith

/-! ## Boundary Jacobi recurrence -/

private theorem shiftedLegendreReal_recurrence_seven :
    (8 : ℝ) • shiftedLegendreReal 8 =
      (15 : ℝ) • ((1 - 2 * X) * shiftedLegendreReal 7) -
        (7 : ℝ) • shiftedLegendreReal 6 := by
  apply Polynomial.funext
  intro x
  simp [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Finset.sum_range_succ, Polynomial.smul_eq_C_mul]
  norm_num [Nat.choose]
  ring

private theorem shiftedLegendreReal_recurrence_eight :
    (9 : ℝ) • shiftedLegendreReal 9 =
      (17 : ℝ) • ((1 - 2 * X) * shiftedLegendreReal 8) -
        (8 : ℝ) • shiftedLegendreReal 7 := by
  apply Polynomial.funext
  intro x
  simp [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Finset.sum_range_succ, Polynomial.smul_eq_C_mul]
  norm_num [Nat.choose]
  ring

private theorem shiftedLegendreReal_recurrence_nine :
    (10 : ℝ) • shiftedLegendreReal 10 =
      (19 : ℝ) • ((1 - 2 * X) * shiftedLegendreReal 9) -
        (9 : ℝ) • shiftedLegendreReal 8 := by
  apply Polynomial.funext
  intro x
  simp [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Finset.sum_range_succ, Polynomial.smul_eq_C_mul]
  norm_num [Nat.choose]
  ring

private theorem shiftedLegendreReal_recurrence_ten :
    (11 : ℝ) • shiftedLegendreReal 11 =
      (21 : ℝ) • ((1 - 2 * X) * shiftedLegendreReal 10) -
        (10 : ℝ) • shiftedLegendreReal 9 := by
  apply Polynomial.funext
  intro x
  simp [shiftedLegendreReal, Polynomial.shiftedLegendre,
    Finset.sum_range_succ, Polynomial.smul_eq_C_mul]
  norm_num [Nat.choose]
  ring

private theorem centeredX_mul_shiftedLegendreReal_seven :
    (2 * X - 1) * shiftedLegendreReal 7 =
      -(8 / 15 : ℝ) • shiftedLegendreReal 8 -
        (7 / 15 : ℝ) • shiftedLegendreReal 6 := by
  apply Polynomial.funext
  intro x
  have h := congrArg (fun p : ℝ[X] ↦ p.eval x)
    shiftedLegendreReal_recurrence_seven
  simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat,
    Polynomial.eval_X] at h ⊢
  linarith

private theorem centeredX_mul_shiftedLegendreReal_nine :
    (2 * X - 1) * shiftedLegendreReal 9 =
      -(9 / 19 : ℝ) • shiftedLegendreReal 8 -
        (10 / 19 : ℝ) • shiftedLegendreReal 10 := by
  apply Polynomial.funext
  intro x
  have h := congrArg (fun p : ℝ[X] ↦ p.eval x)
    shiftedLegendreReal_recurrence_nine
  simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat,
    Polynomial.eval_X] at h ⊢
  linarith

/-- Multiplication by the centered coordinate `1 - 2t` on a basis
polynomial, transported to `L²[0,1]`. -/
private def centeredMulShiftedLegendreL2 (n : ℕ) : UnitIntervalL2 :=
  polynomialToL2 ((1 - 2 * X) * shiftedLegendreReal n)

private theorem inner_centeredMulShiftedLegendreL2_symm (m n : ℕ) :
    inner ℝ (centeredMulShiftedLegendreL2 m) (shiftedLegendreL2 n) =
      inner ℝ (shiftedLegendreL2 m) (centeredMulShiftedLegendreL2 n) := by
  let pm := polynomialToContinuous ((1 - 2 * X) * shiftedLegendreReal m)
  let pn := polynomialToContinuous (shiftedLegendreReal n)
  let qm := polynomialToContinuous (shiftedLegendreReal m)
  let qn := polynomialToContinuous ((1 - 2 * X) * shiftedLegendreReal n)
  have hleft := MeasureTheory.ContinuousMap.inner_toLp
    (𝕜 := ℝ) (volume : Measure unitInterval) pm pn
  have hright := MeasureTheory.ContinuousMap.inner_toLp
    (𝕜 := ℝ) (volume : Measure unitInterval) qm qn
  change inner ℝ
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ pm)
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ pn) =
    inner ℝ
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ qm)
    (ContinuousMap.toLp 2 (volume : Measure unitInterval) ℝ qn)
  calc
    _ = ∫ t : unitInterval, pn t * starRingEnd ℝ (pm t) := hleft
    _ = ∫ t : unitInterval, qn t * starRingEnd ℝ (qm t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp only [pm, pn, qm, qn]
      change (shiftedLegendreReal n).eval (t : ℝ) *
          (((1 - 2 * X) * shiftedLegendreReal m).eval (t : ℝ)) =
        (((1 - 2 * X) * shiftedLegendreReal n).eval (t : ℝ)) *
          (shiftedLegendreReal m).eval (t : ℝ)
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one,
        Polynomial.eval_ofNat, Polynomial.eval_X]
      ring
    _ = _ := hright.symm

private theorem shiftedLegendreL2_recurrence_seven :
    (8 : ℝ) • shiftedLegendreL2 8 =
      (15 : ℝ) • centeredMulShiftedLegendreL2 7 -
        (7 : ℝ) • shiftedLegendreL2 6 := by
  simpa only [shiftedLegendreL2, centeredMulShiftedLegendreL2,
    map_smul, map_sub] using
      congrArg polynomialToL2 shiftedLegendreReal_recurrence_seven

private theorem shiftedLegendreL2_recurrence_eight :
    (9 : ℝ) • shiftedLegendreL2 9 =
      (17 : ℝ) • centeredMulShiftedLegendreL2 8 -
        (8 : ℝ) • shiftedLegendreL2 7 := by
  simpa only [shiftedLegendreL2, centeredMulShiftedLegendreL2,
    map_smul, map_sub] using
      congrArg polynomialToL2 shiftedLegendreReal_recurrence_eight

private theorem shiftedLegendreL2_recurrence_nine :
    (10 : ℝ) • shiftedLegendreL2 10 =
      (19 : ℝ) • centeredMulShiftedLegendreL2 9 -
        (9 : ℝ) • shiftedLegendreL2 8 := by
  simpa only [shiftedLegendreL2, centeredMulShiftedLegendreL2,
    map_smul, map_sub] using
      congrArg polynomialToL2 shiftedLegendreReal_recurrence_nine

private theorem shiftedLegendreL2_recurrence_ten :
    (11 : ℝ) • shiftedLegendreL2 11 =
      (21 : ℝ) • centeredMulShiftedLegendreL2 10 -
        (10 : ℝ) • shiftedLegendreL2 9 := by
  simpa only [shiftedLegendreL2, centeredMulShiftedLegendreL2,
    map_smul, map_sub] using
      congrArg polynomialToL2 shiftedLegendreReal_recurrence_ten

private theorem norm_sq_shiftedLegendreL2_eight_eq_ratio_seven :
    ‖shiftedLegendreL2 8‖ ^ 2 =
      (15 / 17 : ℝ) * ‖shiftedLegendreL2 7‖ ^ 2 := by
  have h7 := congrArg
    (fun z : UnitIntervalL2 ↦ inner ℝ z (shiftedLegendreL2 8))
    shiftedLegendreL2_recurrence_seven
  have h8 := congrArg
    (fun z : UnitIntervalL2 ↦ inner ℝ (shiftedLegendreL2 7) z)
    shiftedLegendreL2_recurrence_eight
  have hsym := inner_centeredMulShiftedLegendreL2_symm 7 8
  have h68 := inner_shiftedLegendreL2_eq_zero (by norm_num : 6 ≠ 8)
  have h79 := inner_shiftedLegendreL2_eq_zero (by norm_num : 7 ≠ 9)
  simp only [real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at h7 h8
  rw [h68, mul_zero, sub_zero, hsym] at h7
  rw [h79, mul_zero] at h8
  nlinarith

private theorem norm_sq_shiftedLegendreL2_nine_eq_ratio_eight :
    ‖shiftedLegendreL2 9‖ ^ 2 =
      (17 / 19 : ℝ) * ‖shiftedLegendreL2 8‖ ^ 2 := by
  have h8 := congrArg
    (fun z : UnitIntervalL2 ↦ inner ℝ z (shiftedLegendreL2 9))
    shiftedLegendreL2_recurrence_eight
  have h9 := congrArg
    (fun z : UnitIntervalL2 ↦ inner ℝ (shiftedLegendreL2 8) z)
    shiftedLegendreL2_recurrence_nine
  have hsym := inner_centeredMulShiftedLegendreL2_symm 8 9
  have h79 := inner_shiftedLegendreL2_eq_zero (by norm_num : 7 ≠ 9)
  have h810 := inner_shiftedLegendreL2_eq_zero (by norm_num : 8 ≠ 10)
  simp only [real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at h8 h9
  rw [h79, mul_zero, sub_zero, hsym] at h8
  rw [h810, mul_zero] at h9
  nlinarith

private theorem norm_sq_shiftedLegendreL2_ten_eq_ratio_nine :
    ‖shiftedLegendreL2 10‖ ^ 2 =
      (19 / 21 : ℝ) * ‖shiftedLegendreL2 9‖ ^ 2 := by
  have h9 := congrArg
    (fun z : UnitIntervalL2 ↦ inner ℝ z (shiftedLegendreL2 10))
    shiftedLegendreL2_recurrence_nine
  have h10 := congrArg
    (fun z : UnitIntervalL2 ↦ inner ℝ (shiftedLegendreL2 9) z)
    shiftedLegendreL2_recurrence_ten
  have hsym := inner_centeredMulShiftedLegendreL2_symm 9 10
  have h810 := inner_shiftedLegendreL2_eq_zero (by norm_num : 8 ≠ 10)
  have h911 := inner_shiftedLegendreL2_eq_zero (by norm_num : 9 ≠ 11)
  simp only [real_inner_smul_left, real_inner_smul_right,
    inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at h9 h10
  rw [h810, mul_zero, sub_zero, hsym] at h9
  rw [h911, mul_zero] at h10
  nlinarith

private def boundaryJacobiA7 : ℝ :=
  (8 / 15 : ℝ) * ‖shiftedLegendreL2 8‖ / ‖shiftedLegendreL2 7‖

private def boundaryJacobiA8 : ℝ :=
  (9 / 19 : ℝ) * ‖shiftedLegendreL2 8‖ / ‖shiftedLegendreL2 9‖

private def boundaryJacobiA9 : ℝ :=
  (10 / 19 : ℝ) * ‖shiftedLegendreL2 10‖ / ‖shiftedLegendreL2 9‖

private theorem boundaryJacobiA7_sq :
    boundaryJacobiA7 ^ 2 = (64 / 255 : ℝ) := by
  have hratio := norm_sq_shiftedLegendreL2_eight_eq_ratio_seven
  have hne : ‖shiftedLegendreL2 7‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (shiftedLegendreL2_ne_zero 7)
  unfold boundaryJacobiA7
  field_simp [hne]
  nlinarith

private theorem boundaryJacobiA8_sq :
    boundaryJacobiA8 ^ 2 = (81 / 323 : ℝ) := by
  have hratio := norm_sq_shiftedLegendreL2_nine_eq_ratio_eight
  have hne : ‖shiftedLegendreL2 9‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (shiftedLegendreL2_ne_zero 9)
  unfold boundaryJacobiA8
  field_simp [hne]
  nlinarith

private theorem boundaryJacobiA9_sq :
    boundaryJacobiA9 ^ 2 = (100 / 399 : ℝ) := by
  have hratio := norm_sq_shiftedLegendreL2_ten_eq_ratio_nine
  have hne : ‖shiftedLegendreL2 9‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (shiftedLegendreL2_ne_zero 9)
  unfold boundaryJacobiA9
  field_simp [hne]
  nlinarith

private def shiftedLegendrePairing (f : unitInterval → ℝ) (n : ℕ) : ℝ :=
  ∫ t : unitInterval, f t * (shiftedLegendreReal n).eval (t : ℝ)

private theorem integrable_shiftedLegendrePairing
    (f : unitInterval → ℝ) (hf : Continuous f) (n : ℕ) :
    Integrable (fun t : unitInterval ↦
      f t * (shiftedLegendreReal n).eval (t : ℝ)) := by
  exact (hf.mul (by fun_prop)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem shiftedLegendrePairing_eq_norm_mul_repr
    (f : unitInterval → ℝ) (hf : MemLp f 2) (n : ℕ) :
    shiftedLegendrePairing f n =
      ‖shiftedLegendreL2 n‖ *
        shiftedLegendreHilbertBasis.repr (hf.toLp f) n := by
  have hrepr := shiftedLegendreHilbertBasis_repr_eq f hf n
  have hne : ‖shiftedLegendreL2 n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (shiftedLegendreL2_ne_zero n)
  rw [hrepr]
  unfold shiftedLegendrePairing
  rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]

private theorem shiftedLegendrePairing_centeredCoordinate_seven
    (f : unitInterval → ℝ) (hf : Continuous f) :
    shiftedLegendrePairing (fun t ↦ (2 * (t : ℝ) - 1) * f t) 7 =
      -(8 / 15 : ℝ) * shiftedLegendrePairing f 8 -
        (7 / 15 : ℝ) * shiftedLegendrePairing f 6 := by
  have h8 := integrable_shiftedLegendrePairing f hf 8
  have h6 := integrable_shiftedLegendrePairing f hf 6
  unfold shiftedLegendrePairing
  rw [show (fun t : unitInterval ↦
      ((2 * (t : ℝ) - 1) * f t) *
        (shiftedLegendreReal 7).eval (t : ℝ)) =
      fun t ↦ -(8 / 15 : ℝ) *
          (f t * (shiftedLegendreReal 8).eval (t : ℝ)) -
        (7 / 15 : ℝ) *
          (f t * (shiftedLegendreReal 6).eval (t : ℝ)) by
    funext t
    have h := congrArg (fun p : ℝ[X] ↦ p.eval (t : ℝ))
      centeredX_mul_shiftedLegendreReal_seven
    simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat,
      Polynomial.eval_X] at h
    linear_combination (f t) * h,
    integral_sub (h8.const_mul _) (h6.const_mul _),
    integral_const_mul, integral_const_mul]

private theorem shiftedLegendrePairing_centeredCoordinate_nine
    (f : unitInterval → ℝ) (hf : Continuous f) :
    shiftedLegendrePairing (fun t ↦ (2 * (t : ℝ) - 1) * f t) 9 =
      -(9 / 19 : ℝ) * shiftedLegendrePairing f 8 -
        (10 / 19 : ℝ) * shiftedLegendrePairing f 10 := by
  have h8 := integrable_shiftedLegendrePairing f hf 8
  have h10 := integrable_shiftedLegendrePairing f hf 10
  unfold shiftedLegendrePairing
  rw [show (fun t : unitInterval ↦
      ((2 * (t : ℝ) - 1) * f t) *
        (shiftedLegendreReal 9).eval (t : ℝ)) =
      fun t ↦ -(9 / 19 : ℝ) *
          (f t * (shiftedLegendreReal 8).eval (t : ℝ)) -
        (10 / 19 : ℝ) *
          (f t * (shiftedLegendreReal 10).eval (t : ℝ)) by
    funext t
    have h := congrArg (fun p : ℝ[X] ↦ p.eval (t : ℝ))
      centeredX_mul_shiftedLegendreReal_nine
    simp only [Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat,
      Polynomial.eval_X] at h
    linear_combination (f t) * h,
    integral_sub (h8.const_mul _) (h10.const_mul _),
    integral_const_mul, integral_const_mul]

private theorem repr_centeredCoordinate_seven
    (f : unitInterval → ℝ) (hfcont : Continuous f)
    (hf : MemLp f 2)
    (hg : MemLp (fun t : unitInterval ↦ (2 * (t : ℝ) - 1) * f t) 2)
    (h6 : shiftedLegendreHilbertBasis.repr (hf.toLp f) 6 = 0) :
    shiftedLegendreHilbertBasis.repr
        (hg.toLp (fun t : unitInterval ↦ (2 * (t : ℝ) - 1) * f t)) 7 =
      -boundaryJacobiA7 *
        shiftedLegendreHilbertBasis.repr (hf.toLp f) 8 := by
  have hpair := shiftedLegendrePairing_centeredCoordinate_seven f hfcont
  rw [shiftedLegendrePairing_eq_norm_mul_repr _ hg 7,
    shiftedLegendrePairing_eq_norm_mul_repr f hf 8,
    shiftedLegendrePairing_eq_norm_mul_repr f hf 6, h6, mul_zero,
    mul_zero, sub_zero] at hpair
  have hne : ‖shiftedLegendreL2 7‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (shiftedLegendreL2_ne_zero 7)
  unfold boundaryJacobiA7
  field_simp [hne] at ⊢
  nlinarith

private theorem repr_centeredCoordinate_nine
    (f : unitInterval → ℝ) (hfcont : Continuous f)
    (hf : MemLp f 2)
    (hg : MemLp (fun t : unitInterval ↦ (2 * (t : ℝ) - 1) * f t) 2) :
    shiftedLegendreHilbertBasis.repr
        (hg.toLp (fun t : unitInterval ↦ (2 * (t : ℝ) - 1) * f t)) 9 =
      -(boundaryJacobiA8 *
          shiftedLegendreHilbertBasis.repr (hf.toLp f) 8 +
        boundaryJacobiA9 *
          shiftedLegendreHilbertBasis.repr (hf.toLp f) 10) := by
  have hpair := shiftedLegendrePairing_centeredCoordinate_nine f hfcont
  rw [shiftedLegendrePairing_eq_norm_mul_repr _ hg 9,
    shiftedLegendrePairing_eq_norm_mul_repr f hf 8,
    shiftedLegendrePairing_eq_norm_mul_repr f hf 10] at hpair
  have hne : ‖shiftedLegendreL2 9‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (shiftedLegendreL2_ne_zero 9)
  unfold boundaryJacobiA8 boundaryJacobiA9
  field_simp [hne] at ⊢
  nlinarith

private theorem boundaryJacobi_two_by_two
    (c d : ℝ) :
    (1 / 5 : ℝ) * (c ^ 2 + d ^ 2) ≤
      2 * ((harmonic 10 : ℝ) - harmonic 8) * d ^ 2 +
        (1 / 2 : ℝ) *
          (boundaryJacobiA7 ^ 2 * c ^ 2 +
            (boundaryJacobiA8 * c + boundaryJacobiA9 * d) ^ 2) := by
  let q00 : ℝ := (1 / 2 : ℝ) *
    (boundaryJacobiA7 ^ 2 + boundaryJacobiA8 ^ 2) - 1 / 5
  let q02 : ℝ := (1 / 2 : ℝ) * boundaryJacobiA8 * boundaryJacobiA9
  let q22 : ℝ := 2 * ((harmonic 10 : ℝ) - harmonic 8) +
    (1 / 2 : ℝ) * boundaryJacobiA9 ^ 2 - 1 / 5
  have h00 : q00 = (29 / 570 : ℝ) := by
    dsimp only [q00]
    rw [boundaryJacobiA7_sq, boundaryJacobiA8_sq]
    norm_num
  have h22 : q22 = (416 / 1197 : ℝ) := by
    dsimp only [q22]
    rw [boundaryJacobiA9_sq]
    norm_num [harmonic, Finset.sum_range_succ]
  have h02sq : q02 ^ 2 = (675 / 42959 : ℝ) := by
    dsimp only [q02]
    rw [mul_pow, mul_pow, boundaryJacobiA8_sq, boundaryJacobiA9_sq]
    norm_num
  have hfirst : 0 < q00 := by rw [h00]; norm_num
  have hdet : 0 < q00 * q22 - q02 ^ 2 := by
    rw [h00, h22, h02sq]
    norm_num
  have hquad := quadratic_add_tail_nonneg
    q00 q02 q22 0 0 0 c d hfirst hdet (by norm_num)
  dsimp only [q00, q02, q22] at hquad
  norm_num [harmonic, Finset.sum_range_succ] at hquad ⊢
  nlinarith

private theorem boundaryJacobi_with_tail
    (c d T : ℝ) (hdT : d ^ 2 ≤ T) :
    (1 / 5 : ℝ) * (c ^ 2 + T) ≤
      2 * ((harmonic 10 : ℝ) - harmonic 8) * T +
        (1 / 2 : ℝ) *
          (boundaryJacobiA7 ^ 2 * c ^ 2 +
            (boundaryJacobiA8 * c + boundaryJacobiA9 * d) ^ 2) := by
  have hboundary := boundaryJacobi_two_by_two c d
  norm_num [harmonic, Finset.sum_range_succ] at hboundary ⊢
  nlinarith

private theorem harmonic_ten_norm_sq_le_logEnergy_add_boundary
    (f : unitInterval → ℝ) (hf : MemLp f 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand f))
    (hlow : ∀ n < 8,
      shiftedLegendreHilbertBasis.repr (hf.toLp f) n = 0)
    (hodd : ∀ n, Odd n →
      shiftedLegendreHilbertBasis.repr (hf.toLp f) n = 0) :
    (2 * (harmonic 10 : ℝ)) * ‖hf.toLp f‖ ^ 2 ≤
      unitIntervalLogEnergy f +
        2 * ((harmonic 10 : ℝ) - harmonic 8) *
          shiftedLegendreHilbertBasis.repr (hf.toLp f) 8 ^ 2 := by
  classical
  let F : UnitIntervalL2 := hf.toLp f
  let delta : ℝ := 2 * ((harmonic 10 : ℝ) - harmonic 8)
  let corr : ℝ := delta * shiftedLegendreHilbertBasis.repr F 8 ^ 2
  have hdelta : 0 ≤ delta := by
    dsimp only [delta]
    have hH := harmonic_cast_mono (by norm_num : 8 ≤ 10)
    linarith
  have hcorr : 0 ≤ corr :=
    mul_nonneg hdelta (sq_nonneg _)
  have hfinite : ∀ N : ℕ,
      (2 * (harmonic 10 : ℝ)) * shiftedLegendrePartialNormSq F N ≤
        unitIntervalLogEnergy f + corr := by
    intro N
    have hterm : ∀ n ∈ Finset.range N,
        (2 * (harmonic 10 : ℝ)) *
            shiftedLegendreHilbertBasis.repr F n ^ 2 ≤
          (2 * (harmonic n : ℝ)) *
              shiftedLegendreHilbertBasis.repr F n ^ 2 +
            if n = 8 then corr else 0 := by
      intro n _hn
      by_cases hnlow : n < 8
      · have hz : shiftedLegendreHilbertBasis.repr F n = 0 := by
          simpa only [F] using hlow n hnlow
        have hn8 : n ≠ 8 := by omega
        simp [hz, hn8]
      · by_cases hn8 : n = 8
        · subst n
          simp only [if_pos]
          dsimp only [corr, delta]
          ring_nf
          exact le_rfl
        · by_cases hn9 : n = 9
          · subst n
            have hz : shiftedLegendreHilbertBasis.repr F 9 = 0 := by
              simpa only [F] using hodd 9 (by norm_num)
            simp [hz]
          · have hn10 : 10 ≤ n := by omega
            have hH := harmonic_cast_mono hn10
            simp only [if_neg hn8, add_zero]
            exact mul_le_mul_of_nonneg_right (by nlinarith)
              (sq_nonneg _)
    have hindicator :
        (∑ n ∈ Finset.range N, if n = 8 then corr else 0) ≤ corr := by
      by_cases hmem : 8 ∈ Finset.range N
      · simp [hmem]
      · simp [hmem, hcorr]
    have hspectral := partialSpectralEnergy_le_unitIntervalLogEnergy
      f hf henergy N
    change (∑ n ∈ Finset.range N,
        (2 * (harmonic n : ℝ)) *
          shiftedLegendreHilbertBasis.repr F n ^ 2) ≤
      unitIntervalLogEnergy f at hspectral
    change (2 * (harmonic 10 : ℝ)) *
        (∑ n ∈ Finset.range N,
          shiftedLegendreHilbertBasis.repr F n ^ 2) ≤
      unitIntervalLogEnergy f + corr
    rw [Finset.mul_sum]
    calc
      (∑ n ∈ Finset.range N,
          (2 * (harmonic 10 : ℝ)) *
            shiftedLegendreHilbertBasis.repr F n ^ 2) ≤
          ∑ n ∈ Finset.range N,
            ((2 * (harmonic n : ℝ)) *
                shiftedLegendreHilbertBasis.repr F n ^ 2 +
              if n = 8 then corr else 0) :=
        Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.range N,
            (2 * (harmonic n : ℝ)) *
              shiftedLegendreHilbertBasis.repr F n ^ 2) +
          (∑ n ∈ Finset.range N, if n = 8 then corr else 0) := by
        rw [Finset.sum_add_distrib]
      _ ≤ (∑ n ∈ Finset.range N,
            (2 * (harmonic n : ℝ)) *
              shiftedLegendreHilbertBasis.repr F n ^ 2) + corr :=
        add_le_add le_rfl hindicator
      _ ≤ unitIntervalLogEnergy f + corr :=
        add_le_add hspectral le_rfl
  dsimp only [F, corr, delta] at hfinite ⊢
  apply le_of_tendsto
    ((tendsto_shiftedLegendrePartialNormSq (hf.toLp f)).const_mul
      (2 * (harmonic 10 : ℝ)))
  exact Filter.Eventually.of_forall hfinite

private theorem two_repr_sq_le_norm_sq
    (F : UnitIntervalL2) (m n : ℕ) (hmn : m ≠ n) :
    shiftedLegendreHilbertBasis.repr F m ^ 2 +
        shiftedLegendreHilbertBasis.repr F n ^ 2 ≤
      ‖F‖ ^ 2 := by
  classical
  have hbessel := shiftedLegendreHilbertBasis.orthonormal.sum_inner_products_le
    F (s := {m, n})
  have hm := shiftedLegendreHilbertBasis.repr_apply_apply F m
  have hn := shiftedLegendreHilbertBasis.repr_apply_apply F n
  rw [Finset.sum_insert (by simpa using hmn), Finset.sum_singleton,
    ← hm, ← hn] at hbessel
  simpa only [Real.norm_eq_abs, sq_abs] using hbessel

private theorem boundary_pairing_bessel
    (f : unitInterval → ℝ) (hfcont : Continuous f)
    (hf : MemLp f 2)
    (hg : MemLp (fun t : unitInterval ↦ (2 * (t : ℝ) - 1) * f t) 2)
    (h6 : shiftedLegendreHilbertBasis.repr (hf.toLp f) 6 = 0) :
    boundaryJacobiA7 ^ 2 *
          shiftedLegendreHilbertBasis.repr (hf.toLp f) 8 ^ 2 +
        (boundaryJacobiA8 *
            shiftedLegendreHilbertBasis.repr (hf.toLp f) 8 +
          boundaryJacobiA9 *
            shiftedLegendreHilbertBasis.repr (hf.toLp f) 10) ^ 2 ≤
      ‖hg.toLp (fun t : unitInterval ↦ (2 * (t : ℝ) - 1) * f t)‖ ^ 2 := by
  let G := hg.toLp (fun t : unitInterval ↦ (2 * (t : ℝ) - 1) * f t)
  have hbessel := two_repr_sq_le_norm_sq G 7 9 (by norm_num)
  have h7 := repr_centeredCoordinate_seven f hfcont hf hg h6
  have h9 := repr_centeredCoordinate_nine f hfcont hf hg
  change shiftedLegendreHilbertBasis.repr G 7 = _ at h7
  change shiftedLegendreHilbertBasis.repr G 9 = _ at h9
  rw [h7, h9] at hbessel
  dsimp only [G] at hbessel ⊢
  nlinarith

private theorem integral_centeredCoordinate_sq_le_intrinsicPotential
    (w : ℝ → ℝ) (hw : Continuous w) :
    (∫ t : unitInterval,
        ((2 * (t : ℝ) - 1) * centeredPullback w (t : ℝ)) ^ 2) ≤
      factorTwoIntrinsicPotentialEnergy w := by
  let u : ℝ → ℝ := fun x ↦ x * w x
  have hbridge := integral_unitInterval_centeredPullback_sq u
  have hbridge' :
      (∫ t : unitInterval,
          ((2 * (t : ℝ) - 1) * centeredPullback w (t : ℝ)) ^ 2) =
        (1 / 2 : ℝ) * ∫ x : ℝ in -1..1, (x * w x) ^ 2 := by
    simpa only [u, centeredPullback, mul_assoc] using hbridge
  have hleft : IntervalIntegrable
      (fun x : ℝ ↦ (1 / 2 : ℝ) * (x * w x) ^ 2)
      volume (-1) 1 := by
    exact (by fun_prop : Continuous
      (fun x : ℝ ↦ (1 / 2 : ℝ) * (x * w x) ^ 2)).intervalIntegrable _ _
  have hpotential := intervalIntegrable_endpointPotential_mul_sq w hw
  have hmono :
      (∫ x : ℝ in -1..1, (1 / 2 : ℝ) * (x * w x) ^ 2) ≤
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num) hleft hpotential
    intro x hx
    have hquartic := quartic_le_endpointPotential
      (show |x| < 1 by rw [abs_lt]; exact hx)
    have hscaled := mul_le_mul_of_nonneg_right hquartic (sq_nonneg (w x))
    unfold yoshidaEndpointQuartic at hscaled
    nlinarith [sq_nonneg x, sq_nonneg (w x), sq_nonneg (x ^ 2 * w x)]
  unfold factorTwoIntrinsicPotentialEnergy
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [hbridge']
  exact hmono

/-- The first surviving even mode at cutoff eight receives a structural
`1 / 10` reserve from the endpoint potential.  Only the boundary Jacobi
coupling `P₈/P₁₀` is isolated; every higher mode is controlled at once by
harmonic monotonicity. -/
theorem harmonic_eight_add_one_tenth_mul_intrinsicEnergy_le_raw_add_half_potential
    (w : ℝ → ℝ) (hw : Continuous w) (hweven : Function.Even w)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w)
    (hlow : centeredLegendreMomentsVanishBelow w 8) :
    ((harmonic 8 : ℝ) + 1 / 10) * factorTwoIntrinsicEnergy w ≤
      centeredRawLogEnergy w / 4 +
        (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy w := by
  obtain ⟨C, hLip⟩ := exists_lipschitzWith_centeredPullback w hlocal
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  let g : unitInterval → ℝ := fun t ↦ (2 * (t : ℝ) - 1) * f t
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hgcont : Continuous g := by
    dsimp only [g]
    fun_prop
  have hf : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hg : MemLp g 2 :=
    hgcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  let F : UnitIntervalL2 := hf.toLp f
  let G : UnitIntervalL2 := hg.toLp g
  let c : ℝ := shiftedLegendreHilbertBasis.repr F 8
  let d : ℝ := shiftedLegendreHilbertBasis.repr F 10
  let T : ℝ := ‖F‖ ^ 2 - c ^ 2
  have hreprLow : ∀ n < 8,
      shiftedLegendreHilbertBasis.repr F n = 0 := by
    intro n hn
    rw [shiftedLegendreHilbertBasis_repr_eq f hf n]
    have hm : shiftedLegendrePairing f n = 0 := by
      simpa only [shiftedLegendrePairing, f] using hlow n hn
    rw [show (∫ t : unitInterval,
        f t * (shiftedLegendreReal n).eval (t : ℝ)) =
          shiftedLegendrePairing f n by rfl, hm, mul_zero]
  have hreprOdd : ∀ n, Odd n →
      shiftedLegendreHilbertBasis.repr F n = 0 := by
    intro n hn
    simpa only [F, f] using
      centeredPullback_repr_eq_zero_of_even_of_odd w hf hweven n hn
  have hraw := harmonic_ten_norm_sq_le_logEnergy_add_boundary
    f hf henergy hreprLow hreprOdd
  change (2 * (harmonic 10 : ℝ)) * ‖F‖ ^ 2 ≤
      unitIntervalLogEnergy f +
        2 * ((harmonic 10 : ℝ) - harmonic 8) * c ^ 2 at hraw
  have hcd := two_repr_sq_le_norm_sq F 8 10 (by norm_num)
  change c ^ 2 + d ^ 2 ≤ ‖F‖ ^ 2 at hcd
  have hdT : d ^ 2 ≤ T := by
    dsimp only [T]
    linarith
  have hboundary := boundaryJacobi_with_tail c d T hdT
  have h6 : shiftedLegendreHilbertBasis.repr F 6 = 0 :=
    hreprLow 6 (by norm_num)
  have hGbessel := boundary_pairing_bessel f hfcont hf hg h6
  change boundaryJacobiA7 ^ 2 * c ^ 2 +
        (boundaryJacobiA8 * c + boundaryJacobiA9 * d) ^ 2 ≤
      ‖G‖ ^ 2 at hGbessel
  have hboundary' :
      (1 / 5 : ℝ) * ‖F‖ ^ 2 ≤
        2 * ((harmonic 10 : ℝ) - harmonic 8) * T +
          (1 / 2 : ℝ) * ‖G‖ ^ 2 := by
    have hT : c ^ 2 + T = ‖F‖ ^ 2 := by
      dsimp only [T]
      ring
    rw [hT] at hboundary
    nlinarith
  have hraw' :
      2 * (harmonic 8 : ℝ) * ‖F‖ ^ 2 +
          2 * ((harmonic 10 : ℝ) - harmonic 8) * T ≤
        unitIntervalLogEnergy f := by
    dsimp only [T] at ⊢
    nlinarith
  have hunit :
      2 * ((harmonic 8 : ℝ) + 1 / 10) * ‖F‖ ^ 2 ≤
        unitIntervalLogEnergy f + (1 / 2 : ℝ) * ‖G‖ ^ 2 := by
    nlinarith
  have hGnorm := norm_sq_toLp_eq_integral_sq g hg
  have hpotential := integral_centeredCoordinate_sq_le_intrinsicPotential w hw
  have hGpotential : ‖G‖ ^ 2 ≤ factorTwoIntrinsicPotentialEnergy w := by
    change ‖hg.toLp g‖ ^ 2 ≤ factorTwoIntrinsicPotentialEnergy w
    rw [hGnorm]
    simpa only [g, f] using hpotential
  have hunitPotential :
      2 * ((harmonic 8 : ℝ) + 1 / 10) * ‖F‖ ^ 2 ≤
        unitIntervalLogEnergy f +
          (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy w := by
    nlinarith
  have hFnorm := norm_sq_toLp_eq_integral_sq f hf
  change ‖F‖ ^ 2 =
    ∫ t : unitInterval, centeredPullback w (t : ℝ) ^ 2 at hFnorm
  rw [integral_unitInterval_centeredPullback_sq w] at hFnorm
  change ‖F‖ ^ 2 = (1 / 2 : ℝ) * factorTwoIntrinsicEnergy w at hFnorm
  have henergy' : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) := by
    simpa only [f] using henergy
  have hlog : unitIntervalLogEnergy f =
      (1 / 4 : ℝ) * centeredRawLogEnergy w := by
    simpa only [f] using unitIntervalLogEnergy_centeredPullback w henergy'
  rw [hFnorm, hlog] at hunitPotential
  nlinarith

/-- The sharpened projected loss fits the cutoff-eight harmonic reserve once
the structural `1 / 10` potential gain is retained. -/
theorem projectedEvenRemainderLoss_le_harmonic_eight_add_tenth
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    factorTwoIntrinsicProjectedEvenRemainderLoss a b ≤
      (harmonic 8 : ℝ) + 1 / 10 - Real.log 2 / 2 := by
  have hloss := projectedEvenRemainderLoss_lt_4926971_div_2000000 a b hab
  have hlog : Real.log 2 < (7 / 10 : ℝ) :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  norm_num [harmonic, Finset.sum_range_succ] at hloss ⊢
  linarith

/-- Complete phase positivity on the infinite structural residual above
even cutoff eight and odd cutoff nine.  The finite low obstruction is
therefore reduced to `P₀,P₂,P₄,P₆` and `P₁,P₃,P₅,P₇`; no retained
phase point or matrix entry is enumerated. -/
theorem factorTwoEndpointChannelPhase_nonneg_of_eight_nine_higher_residual
    (e o : ℝ → ℝ) (hec : Continuous e) (hoc : Continuous o)
    (he : Function.Even e) (ho : Function.Odd o)
    (he0 : centeredEvenP0Coefficient e = 0)
    (helocal : LocallyLipschitzOn (Icc (-1) 1) e)
    (holocal : LocallyLipschitzOn (Icc (-1) 1) o)
    (heLow : centeredLegendreMomentsVanishBelow e 8)
    (hoLow : centeredLegendreMomentsVanishBelow o 9)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 ≤ 1) :
    0 ≤ factorTwoEndpointChannelPhase e o a b := by
  have heReserve :=
    harmonic_eight_add_one_tenth_mul_intrinsicEnergy_le_raw_add_half_potential
      e hec he helocal heLow
  have hoRaw := harmonic_mul_intrinsicEnergy_le_raw_div_four
    o hoc holocal 9 hoLow
  have hprotected := raw_add_half_potential_sub_half_logMass_le_protected
    e o hec hoc helocal holocal a b hab
  have heLoss := projectedEvenRemainderLoss_le_harmonic_eight_add_tenth
    a b hab
  have hoLoss := projectedOddRemainderLoss_le_harmonic_nine a b hab
  have hremainder := neg_factorTwoIntrinsicSignedRemainder_le_projected_energy
    e o hec hoc he ho he0 a b hab
  have heEnergy := factorTwoIntrinsicEnergy_nonneg e
  have hoEnergy := factorTwoIntrinsicEnergy_nonneg o
  have heLossScaled := mul_le_mul_of_nonneg_right heLoss heEnergy
  have hoLossScaled := mul_le_mul_of_nonneg_right hoLoss hoEnergy
  have hoPotential : 0 ≤
      (1 / 2 : ℝ) * factorTwoIntrinsicPotentialEnergy o := by
    exact mul_nonneg (by norm_num)
      (factorTwoIntrinsicPotentialEnergy_nonneg o)
  rw [factorTwoEndpointChannelPhase_eq_protected_add_signedRemainder
    e o hec hoc a b]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineStructural
