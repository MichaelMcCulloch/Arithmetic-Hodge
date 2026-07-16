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
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoPhaseFullProfile
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicProjectedRemainder
open YoshidaFactorTwoPhaseIntrinsicResidual

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

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidualEightNineStructural
