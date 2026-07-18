import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseOddSymmetricBound
import ArithmeticHodge.Analysis.YoshidaRegularKernelSharpMeanZeroSchur

set_option autoImplicit false

open Complex MeasureTheory Polynomial Real Set
open scoped unitInterval

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP7EndpointUpperStructural

noncomputable section

open ShiftedLegendreLogEigen
open ShiftedLegendreLogKernel
open ShiftedLegendreOrthogonality
open UnitIntervalIntegralBridge
open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenFullPolarization
open YoshidaEndpointEvenConstantCross
open YoshidaEndpointEvenTailRepresenter
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaFactorTwoPhaseIntrinsicLow
open YoshidaFactorTwoPhaseIntrinsicResidual
open YoshidaFactorTwoPhaseIntrinsicRemainderBound
open YoshidaFactorTwoPhaseLegendreSixSevenStructuralPositive
open YoshidaFactorTwoPhaseOddSymmetricBound
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRegularKernelSharpMeanZeroSchur
open YoshidaRegularKernelSchur

/-!
# Structural upper bound for the `P7` endpoint diagonal

The seventh centered Legendre mode is treated as one profile.  Its singular
raw energy is evaluated through the all-degree shifted-Legendre eigenvalue;
the remaining pieces use global analytic bounds.  No subdivision or finite
mode enumeration enters the proof.
-/

/-- Exact raw logarithmic energy of the centered seventh Legendre mode. -/
theorem centeredRawLogEnergy_factorTwoCenteredP7_eq :
    centeredRawLogEnergy factorTwoCenteredP7 = (242 / 175 : ℝ) := by
  let p : ℝ[X] := shiftedLegendreReal 7
  let pfun : unitInterval → ℝ := fun t ↦ p.eval (t : ℝ)
  let qfun : unitInterval → ℝ := fun t ↦
    centeredPullback factorTwoCenteredP7 (t : ℝ)
  have hpEnergy : Integrable (unitIntervalRawLogEnergyIntegrand pfun) := by
    simpa only [pfun] using
      integrable_unitIntervalRawLogEnergyIntegrand_polynomial p
  have hqEnergy : Integrable (unitIntervalRawLogEnergyIntegrand qfun) := by
    apply hpEnergy.congr
    filter_upwards [] with z
    unfold unitIntervalRawLogEnergyIntegrand
    dsimp only [pfun, qfun, p]
    rw [centeredPullback_factorTwoCenteredP7,
      centeredPullback_factorTwoCenteredP7]
    ring
  have hqP : unitIntervalLogEnergy qfun = unitIntervalLogEnergy pfun := by
    unfold unitIntervalLogEnergy
    apply congrArg (fun z : ℝ ↦ (1 / 2 : ℝ) * z)
    apply integral_congr_ae
    filter_upwards [] with z
    unfold unitIntervalRawLogEnergyIntegrand
    dsimp only [pfun, qfun, p]
    rw [centeredPullback_factorTwoCenteredP7,
      centeredPullback_factorTwoCenteredP7]
    ring
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
  have hpEigen : (∫ t : unitInterval,
      p.eval (t : ℝ) * (shiftedLogKernel p).eval (t : ℝ)) =
      (2 * (harmonic 7 : ℝ)) *
        ∫ t : unitInterval, p.eval (t : ℝ) * p.eval (t : ℝ) := by
    rw [show shiftedLogKernel p =
        Polynomial.C (2 * (harmonic 7 : ℝ)) * p by
      dsimp only [p]
      exact shiftedLogKernel_shiftedLegendreReal 7]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    ring
  have hbridge := unitIntervalLogEnergy_centeredPullback
    factorTwoCenteredP7 hqEnergy
  change unitIntervalLogEnergy qfun =
    (1 / 4 : ℝ) * centeredRawLogEnergy factorTwoCenteredP7 at hbridge
  have hmass :
      (∫ t : unitInterval, p.eval (t : ℝ) * p.eval (t : ℝ)) =
        (1 / 15 : ℝ) := by
    calc
      _ = ∫ t : unitInterval,
          centeredPullback factorTwoCenteredP7 (t : ℝ) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [] with t
        dsimp only [p]
        rw [centeredPullback_factorTwoCenteredP7]
        ring
      _ = (1 / 2 : ℝ) *
          ∫ x : ℝ in -1..1, factorTwoCenteredP7 x ^ 2 :=
        integral_unitInterval_centeredPullback_sq factorTwoCenteredP7
      _ = (1 / 15 : ℝ) := by
        rw [integral_factorTwoCenteredP7_sq]
        norm_num
  rw [hqP, hpIdentity, hpEigen, hmass] at hbridge
  norm_num [harmonic] at hbridge ⊢
  linarith

private theorem neg_endpoint_mul_regularQuadratic_re_le_log_two_div_sixty_four_energy
    (w : ℝ → ℝ) (hw : Continuous w)
    (hmean : (∫ x : ℝ in -1..1, w x) = 0) :
    -yoshidaEndpointA *
        (yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re ≤
      (Real.log 2 / 64) * factorTwoIntrinsicEnergy w := by
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
  have hre : -(yoshidaEndpointRegularQuadratic f).re ≤
      ‖yoshidaEndpointRegularQuadratic f‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have hscaled := mul_le_mul_of_nonneg_left (hre.trans hnorm)
    yoshidaEndpointA_pos.le
  change -yoshidaEndpointA *
      (yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re ≤ _
  calc
    -yoshidaEndpointA *
          (yoshidaEndpointRegularQuadratic (fun x ↦ (w x : ℂ))).re =
        yoshidaEndpointA *
          (-(yoshidaEndpointRegularQuadratic f).re) := by
      dsimp only [f]
      ring
    _ ≤ yoshidaEndpointA *
          ((1 / 32 : ℝ) * factorTwoIntrinsicEnergy w) := hscaled
    _ = (Real.log 2 / 64) * factorTwoIntrinsicEnergy w := by
      unfold yoshidaEndpointA
      ring

private theorem yoshidaEndpointCoshMoment_eq_centeredCoshMoment
    (w : ℝ → ℝ) :
    yoshidaEndpointCoshMoment w =
      centeredCoshMoment w (yoshidaEndpointA / 2) := by
  unfold centeredCoshMoment yoshidaEndpointCoshMoment
  apply intervalIntegral.integral_congr
  intro x _hx
  ring_nf

/-- Odd parity makes the endpoint hyperbolic rank contribution nonpositive. -/
theorem factorTwoCenteredP7_hyperbolic_nonpos :
    yoshidaEndpointHyperbolicQuadratic
        (fun x ↦ (factorTwoCenteredP7 x : ℂ)) ≤ 0 := by
  have hcosh : yoshidaEndpointCoshMoment factorTwoCenteredP7 = 0 := by
    rw [yoshidaEndpointCoshMoment_eq_centeredCoshMoment]
    exact centeredCoshMoment_eq_zero_of_odd odd_factorTwoCenteredP7
      (yoshidaEndpointA / 2)
  rw [yoshidaEndpointHyperbolicQuadratic_ofReal_eq_moments, hcosh]
  have hA := yoshidaEndpointA_pos
  nlinarith [sq_nonneg (yoshidaEndpointSinhMoment factorTwoCenteredP7)]

/-- The complete positive-phase `P7` diagonal stays below `2/3`.
This is the coarse cap needed to test enhanced low-reserve allocations. -/
theorem factorTwoP7PhaseDiagonal_one_lt_two_thirds :
    factorTwoP7PhaseDiagonal 1 < (2 / 3 : ℝ) := by
  have hmean := centered_interval_integral_eq_zero_of_odd
    factorTwoCenteredP7 odd_factorTwoCenteredP7
  have hregular :=
    neg_endpoint_mul_regularQuadratic_re_le_log_two_div_sixty_four_energy
      factorTwoCenteredP7 continuous_factorTwoCenteredP7 hmean
  rw [factorTwoCenteredP7_energy] at hregular
  have hsym := odd_symmetricPerturbation_le_three_halves_energy
    factorTwoCenteredP7 continuous_factorTwoCenteredP7
      odd_factorTwoCenteredP7
  rw [integral_factorTwoCenteredP7_sq] at hsym
  have hscalar := seven_sixths_lt_yoshidaEndpointScalarMassLoss
  have hlog : (2 / 3 : ℝ) < Real.log 2 :=
    (by norm_num : (2 / 3 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hhyper := factorTwoCenteredP7_hyperbolic_nonpos
  unfold factorTwoP7PhaseDiagonal yoshidaEndpointOddCleanQuadratic
  dsimp only
  rw [centeredRawLogEnergy_factorTwoCenteredP7_eq,
    integral_endpointPotential_mul_factorTwoCenteredP7_sq,
    integral_factorTwoCenteredP7_sq]
  norm_num at hregular hsym ⊢
  nlinarith

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseP7EndpointUpperStructural
