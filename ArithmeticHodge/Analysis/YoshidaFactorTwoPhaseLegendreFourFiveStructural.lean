import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicHigherResidual
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseIntrinsicRemainderBound

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural

open CenteredOddOneThreeEnergy
open UnitIntervalLogEnergyAffine
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOcticPotential
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaEndpointScalarStructuralUpper
open YoshidaFactorTwoPhaseIntrinsicHigherResidual
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseIntrinsicResidual

noncomputable section

/-!
# The first structural middle Legendre pair

These are the first two modes not covered by the intrinsic `P₀/P₂` versus
`P₁/P₃` phase theorem.  The lemmas below package their exact orthogonality,
mass, octic-potential reserve, and raw logarithmic spectral reserve.  They
are the scalar inputs for the first coupled Schur extension.
-/

/-- The centered Legendre polynomial of degree four. -/
def factorTwoCenteredP4 (x : ℝ) : ℝ :=
  (35 * x ^ 4 - 30 * x ^ 2 + 3) / 8

/-- The centered Legendre polynomial of degree five. -/
def factorTwoCenteredP5 (x : ℝ) : ℝ :=
  (63 * x ^ 5 - 70 * x ^ 3 + 15 * x) / 8

theorem continuous_factorTwoCenteredP4 : Continuous factorTwoCenteredP4 := by
  unfold factorTwoCenteredP4
  fun_prop

theorem continuous_factorTwoCenteredP5 : Continuous factorTwoCenteredP5 := by
  unfold factorTwoCenteredP5
  fun_prop

theorem even_factorTwoCenteredP4 : Function.Even factorTwoCenteredP4 := by
  intro x
  unfold factorTwoCenteredP4
  ring

theorem odd_factorTwoCenteredP5 : Function.Odd factorTwoCenteredP5 := by
  intro x
  unfold factorTwoCenteredP5
  ring

theorem locallyLipschitzOn_factorTwoCenteredP4 :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) factorTwoCenteredP4 := by
  have h : ContDiff ℝ 1 factorTwoCenteredP4 := by
    unfold factorTwoCenteredP4
    fun_prop
  exact h.locallyLipschitz.locallyLipschitzOn

theorem locallyLipschitzOn_factorTwoCenteredP5 :
    LocallyLipschitzOn (Icc (-1 : ℝ) 1) factorTwoCenteredP5 := by
  have h : ContDiff ℝ 1 factorTwoCenteredP5 := by
    unfold factorTwoCenteredP5
    fun_prop
  exact h.locallyLipschitz.locallyLipschitzOn

/-! ## Exact polynomial data -/

theorem integral_factorTwoCenteredP4 :
    (∫ x : ℝ in -1..1, factorTwoCenteredP4 x) = 0 := by
  unfold factorTwoCenteredP4
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_factorTwoCenteredP4_mul_centeredEvenP2 :
    (∫ x : ℝ in -1..1,
      factorTwoCenteredP4 x * centeredEvenP2 x) = 0 := by
  unfold factorTwoCenteredP4 centeredEvenP2
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_factorTwoCenteredP5_mul_centeredP1 :
    (∫ x : ℝ in -1..1,
      factorTwoCenteredP5 x * centeredP1 x) = 0 := by
  unfold factorTwoCenteredP5 centeredP1
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_factorTwoCenteredP5_mul_centeredP3 :
    (∫ x : ℝ in -1..1,
      factorTwoCenteredP5 x * centeredP3 x) = 0 := by
  unfold factorTwoCenteredP5 centeredP3
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_factorTwoCenteredP4_sq :
    (∫ x : ℝ in -1..1, factorTwoCenteredP4 x ^ 2) = 2 / 9 := by
  unfold factorTwoCenteredP4
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_factorTwoCenteredP5_sq :
    (∫ x : ℝ in -1..1, factorTwoCenteredP5 x ^ 2) = 2 / 11 := by
  unfold factorTwoCenteredP5
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_octic_mul_factorTwoCenteredP4_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointOctic x * factorTwoCenteredP4 x ^ 2) =
        299911 / 3063060 := by
  unfold yoshidaEndpointOctic factorTwoCenteredP4
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

theorem integral_octic_mul_factorTwoCenteredP5_sq :
    (∫ x : ℝ in -1..1,
      yoshidaEndpointOctic x * factorTwoCenteredP5 x ^ 2) =
        4620263 / 58198140 := by
  unfold yoshidaEndpointOctic factorTwoCenteredP5
  ring_nf
  repeat rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)
    (Continuous.intervalIntegrable (by fun_prop) (-1) 1)]
  repeat rw [intervalIntegral.integral_mul_const]
  repeat rw [integral_pow_nat]
  norm_num

/-! ## Intrinsic coefficients and structural reserves -/

theorem factorTwoCenteredP4_intrinsic_coefficients_zero :
    centeredEvenP0Coefficient factorTwoCenteredP4 = 0 ∧
      centeredEvenP2Coefficient factorTwoCenteredP4 = 0 := by
  constructor
  · unfold centeredEvenP0Coefficient
    rw [integral_factorTwoCenteredP4, mul_zero]
  · unfold centeredEvenP2Coefficient
    rw [integral_factorTwoCenteredP4_mul_centeredEvenP2, mul_zero]

theorem factorTwoCenteredP5_intrinsic_coefficients_zero :
    centeredOddP1Coefficient factorTwoCenteredP5 = 0 ∧
      centeredOddP3Coefficient factorTwoCenteredP5 = 0 := by
  constructor
  · unfold centeredOddP1Coefficient
    rw [integral_factorTwoCenteredP5_mul_centeredP1, mul_zero]
  · unfold centeredOddP3Coefficient
    rw [integral_factorTwoCenteredP5_mul_centeredP3, mul_zero]

theorem factorTwoCenteredP4_raw_reserve :
    (25 / 12 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP4 ≤
      centeredRawLogEnergy factorTwoCenteredP4 / 4 := by
  exact even_intrinsic_residual_raw_reserve
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
    even_factorTwoCenteredP4
    factorTwoCenteredP4_intrinsic_coefficients_zero.1
    factorTwoCenteredP4_intrinsic_coefficients_zero.2
    locallyLipschitzOn_factorTwoCenteredP4

theorem factorTwoCenteredP5_raw_reserve :
    (137 / 60 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP5 ≤
      centeredRawLogEnergy factorTwoCenteredP5 / 4 := by
  exact odd_intrinsic_residual_raw_reserve
    factorTwoCenteredP5 continuous_factorTwoCenteredP5
    odd_factorTwoCenteredP5
    factorTwoCenteredP5_intrinsic_coefficients_zero.1
    factorTwoCenteredP5_intrinsic_coefficients_zero.2
    locallyLipschitzOn_factorTwoCenteredP5

theorem factorTwoCenteredP4_octicPotential_le :
    (299911 / 3063060 : ℝ) ≤
      factorTwoIntrinsicPotentialEnergy factorTwoCenteredP4 := by
  have hoctic : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointOctic x * factorTwoCenteredP4 x ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointOctic factorTwoCenteredP4
    fun_prop
  have hpotential := intervalIntegrable_endpointPotential_mul_sq
    factorTwoCenteredP4 continuous_factorTwoCenteredP4
  rw [← integral_octic_mul_factorTwoCenteredP4_sq]
  unfold factorTwoIntrinsicPotentialEnergy
  apply intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (-1 : ℝ) ≤ 1) hoctic hpotential
  intro x hx
  exact mul_le_mul_of_nonneg_right
    (octic_le_endpointPotential (by simpa only [abs_lt] using hx))
    (sq_nonneg _)

theorem factorTwoCenteredP5_octicPotential_le :
    (4620263 / 58198140 : ℝ) ≤
      factorTwoIntrinsicPotentialEnergy factorTwoCenteredP5 := by
  have hoctic : IntervalIntegrable
      (fun x : ℝ ↦ yoshidaEndpointOctic x * factorTwoCenteredP5 x ^ 2)
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointOctic factorTwoCenteredP5
    fun_prop
  have hpotential := intervalIntegrable_endpointPotential_mul_sq
    factorTwoCenteredP5 continuous_factorTwoCenteredP5
  rw [← integral_octic_mul_factorTwoCenteredP5_sq]
  unfold factorTwoIntrinsicPotentialEnergy
  apply intervalIntegral.integral_mono_on_of_le_Ioo
    (by norm_num : (-1 : ℝ) ≤ 1) hoctic hpotential
  intro x hx
  exact mul_le_mul_of_nonneg_right
    (octic_le_endpointPotential (by simpa only [abs_lt] using hx))
    (sq_nonneg _)

/-! ## Clean diagonal reserves -/

private theorem factorTwoCenteredP4_energy :
    factorTwoIntrinsicEnergy factorTwoCenteredP4 = 2 / 9 := by
  unfold factorTwoIntrinsicEnergy
  exact integral_factorTwoCenteredP4_sq

private theorem factorTwoCenteredP5_energy :
    factorTwoIntrinsicEnergy factorTwoCenteredP5 = 2 / 11 := by
  unfold factorTwoIntrinsicEnergy
  exact integral_factorTwoCenteredP5_sq

/-- The clean diagonal on `P₄` retains a rational `23/20` mass reserve.
Only the global octic potential lower envelope is used. -/
theorem twenty_three_twentieths_energy_le_clean_P4 :
    (23 / 20 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP4 ≤
      yoshidaEndpointOddCleanQuadratic factorTwoCenteredP4 := by
  have hraw := factorTwoCenteredP4_raw_reserve
  have hpotential := factorTwoCenteredP4_octicPotential_le
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hregular :=
    endpoint_mul_regularQuadratic_re_le_log_two_div_sixty_four_energy
      factorTwoCenteredP4 continuous_factorTwoCenteredP4
      integral_factorTwoCenteredP4
  have hhyper := yoshidaEndpointHyperbolicQuadratic_nonneg_of_even
    factorTwoCenteredP4 even_factorTwoCenteredP4
  have hlog : Real.log 2 / 64 < (7 / 640 : ℝ) := by
    have := Real.log_two_lt_d9
    linarith
  rw [factorTwoCenteredP4_energy] at hraw hregular ⊢
  unfold factorTwoIntrinsicPotentialEnergy at hpotential
  unfold yoshidaEndpointOddCleanQuadratic
  rw [integral_factorTwoCenteredP4_sq]
  nlinarith

private theorem hyperbolic_loss_lt_one_sixty_four :
    1 / Real.sqrt 2 - Real.log 2 < (1 / 64 : ℝ) := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLower : (707 / 500 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hinv : 1 / Real.sqrt 2 < (500 / 707 : ℝ) := by
    rw [div_lt_iff₀ hsqrtPos]
    nlinarith
  have hlog := six_hundred_ninety_three_div_thousand_lt_log_two
  linarith

/-- The clean diagonal on `P₅` retains a rational `4/3` mass reserve. -/
theorem four_thirds_energy_le_clean_P5 :
    (4 / 3 : ℝ) * factorTwoIntrinsicEnergy factorTwoCenteredP5 ≤
      yoshidaEndpointOddCleanQuadratic factorTwoCenteredP5 := by
  have hraw := factorTwoCenteredP5_raw_reserve
  have hpotential := factorTwoCenteredP5_octicPotential_le
  have hscalar := yoshidaEndpointScalarMassLoss_lt_338887_div_250000
  have hregular :=
    endpoint_mul_regularQuadratic_re_le_log_two_div_sixty_four_energy
      factorTwoCenteredP5 continuous_factorTwoCenteredP5
      (centered_interval_integral_eq_zero_of_odd
        factorTwoCenteredP5 odd_factorTwoCenteredP5)
  have hhyper := yoshidaEndpointHyperbolicQuadratic_lower
    (fun x ↦ (factorTwoCenteredP5 x : ℂ))
    (Complex.continuous_ofReal.comp continuous_factorTwoCenteredP5)
  have hlog : Real.log 2 / 64 < (7 / 640 : ℝ) := by
    have := Real.log_two_lt_d9
    linarith
  have hdelta := hyperbolic_loss_lt_one_sixty_four
  rw [factorTwoCenteredP5_energy] at hraw hregular ⊢
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hhyper
  rw [integral_factorTwoCenteredP5_sq] at hhyper
  unfold factorTwoIntrinsicPotentialEnergy at hpotential
  unfold yoshidaEndpointOddCleanQuadratic
  rw [integral_factorTwoCenteredP5_sq]
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreFourFiveStructural
