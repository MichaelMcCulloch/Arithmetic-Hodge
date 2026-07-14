import ArithmeticHodge.Analysis.YoshidaEndpointEvenConstantDiagonal
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowHyperbolic
import ArithmeticHodge.Analysis.YoshidaEndpointEvenLowPotential
import ArithmeticHodge.Analysis.YoshidaEndpointQuarticObstruction
import ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledCleanReduction

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankDominationObstruction

noncomputable section

open YoshidaEndpointEvenConstantDiagonal
open YoshidaEndpointEvenLowHyperbolic
open YoshidaEndpointEvenLowPotential
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointQuarticObstruction
open YoshidaFactorTwoEndpointChannelRadius
open YoshidaFactorTwoPhaseCoupledCleanReduction
open YoshidaFactorTwoPhaseCoupledRankLimit
open YoshidaFactorTwoPhaseSymmetricCoercivity
open YoshidaRegularKernelSchur
open YoshidaRenormalizedGeometricKernel
open UnitIntervalLogEnergyAffine

/-!
# Obstruction to phase-independent coupled-rank domination

The manifestly positive rank energy is a useful majorant for the
archimedean phase coordinate, but it is too large to be paid directly by the
clean diagonal.  The constant even profile already gives a structural strict
reverse.  No Fourier cutoff or finite mode computation enters the proof.
-/

theorem constant_clean_lt_eight_fifths :
    yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 1) < (8 / 5 : ℝ) := by
  let R : ℂ := yoshidaEndpointRegularQuadratic (fun _ : ℝ ↦ (1 : ℂ))
  let C : ℝ := ∫ x : ℝ in -1..1,
    Real.cosh (yoshidaEndpointA * x / 2)
  have hlogLower : (2 / 3 : ℝ) < Real.log 2 := by
    exact (by norm_num : (2 / 3 : ℝ) < 693 / 1000).trans
      six_hundred_ninety_three_div_thousand_lt_log_two
  have hlogUpper : Real.log 2 < (7 / 10 : ℝ) := by
    exact log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred.trans
      (by norm_num)
  have hpotential :
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) < (2 / 3 : ℝ) := by
    rw [integral_endpointPotential_one]
    linarith
  have hmass : (7 / 6 : ℝ) < yoshidaEndpointScalarMassLoss := by
    have hgamma := Real.one_half_lt_eulerMascheroniConstant
    have hproduct :=
      three_thousand_six_hundred_forty_seven_div_five_thousand_lt_log_pi_mul_log_two
    unfold yoshidaEndpointScalarMassLoss
    norm_num at hgamma hproduct ⊢
    linarith
  have hRnorm : ‖R‖ ≤ 1 := by
    have h := norm_yoshidaEndpointRegularQuadratic_le
      (fun _ : ℝ ↦ (1 : ℂ)) continuous_const
    norm_num at h ⊢
    exact h
  have hRre : -(1 : ℝ) ≤ R.re := by
    have habs := Complex.abs_re_le_norm R
    linarith [neg_abs_le R.re]
  have hregular : -yoshidaEndpointA * R.re ≤ yoshidaEndpointA := by
    have hscaled := mul_le_mul_of_nonneg_left hRre yoshidaEndpointA_pos.le
    nlinarith
  have hCpos : 0 < C := by
    dsimp only [C]
    exact (by norm_num : (0 : ℝ) < 2).trans
      two_lt_integral_yoshidaEndpoint_cosh
  have hCupper : C < (61 / 30 : ℝ) := by
    simpa only [C] using integral_yoshidaEndpoint_cosh_lt_sixty_one_div_thirty
  have hCsq : C ^ 2 < (61 / 30 : ℝ) ^ 2 := by
    exact (sq_lt_sq₀ hCpos.le (by norm_num)).2 hCupper
  have hAupper : 2 * yoshidaEndpointA < (7 / 10 : ℝ) := by
    unfold yoshidaEndpointA
    linarith
  have hhyperEq :
      yoshidaEndpointHyperbolicQuadratic (fun _ : ℝ ↦ (1 : ℂ)) =
        2 * yoshidaEndpointA * C ^ 2 := by
    have h := yoshidaEndpointHyperbolicQuadratic_zero_two_eq 1 0
    dsimp only [C]
    rw [integral_yoshidaEndpoint_cosh] at ⊢
    simpa using h
  have hhyper :
      yoshidaEndpointHyperbolicQuadratic (fun _ : ℝ ↦ (1 : ℂ)) <
        (29 / 10 : ℝ) := by
    rw [hhyperEq]
    calc
      2 * yoshidaEndpointA * C ^ 2 <
          (7 / 10 : ℝ) * C ^ 2 :=
        mul_lt_mul_of_pos_right hAupper (sq_pos_of_pos hCpos)
      _ < (7 / 10 : ℝ) * (61 / 30 : ℝ) ^ 2 :=
        mul_lt_mul_of_pos_left hCsq (by norm_num)
      _ < (29 / 10 : ℝ) := by norm_num
  rw [yoshidaEndpointOddCleanQuadratic_one_eq]
  dsimp only [R] at hregular
  nlinarith

private theorem twenty_ninths_lt_constant_rank_add_primeBudget :
    (20 / 9 : ℝ) <
      factorTwoCoupledRankEnergy (fun _ : ℝ ↦ 1) (0 : ℝ → ℝ) +
        factorTwoCoupledPrimeMassBudget
          (fun _ : ℝ ↦ 1) (0 : ℝ → ℝ) := by
  let C : ℝ := centeredCoshMoment (fun _ : ℝ ↦ 1)
    (yoshidaEndpointA / 2)
  let tail : ℝ := ∑' m : ℕ,
    Real.exp (-2 * yoshidaEndpointA * oddRate (m + 1)) *
      centeredCoshMoment (fun _ : ℝ ↦ 1)
        (yoshidaEndpointA * oddRate (m + 1)) ^ 2
  have htail : 0 ≤ tail := by
    dsimp only [tail]
    exact tsum_nonneg fun m ↦ mul_nonneg (by positivity) (sq_nonneg _)
  have hRlower :
      yoshidaEndpointA * Real.exp yoshidaEndpointA * C ^ 2 ≤
        factorTwoCoupledRankEnergy
          (fun _ : ℝ ↦ 1) (0 : ℝ → ℝ) := by
    unfold factorTwoCoupledRankEnergy
    simp only [centeredSinhMoment, Pi.zero_apply, mul_zero,
      intervalIntegral.integral_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero]
    dsimp only [C, tail] at htail ⊢
    nlinarith [yoshidaEndpointA_pos]
  have hA : (1 / 3 : ℝ) < yoshidaEndpointA := by
    have hlog := six_hundred_ninety_three_div_thousand_lt_log_two
    unfold yoshidaEndpointA
    norm_num at hlog ⊢
    linarith
  have hC : (2 : ℝ) < C := by
    dsimp only [C, centeredCoshMoment]
    rw [show (fun x : ℝ ↦ Real.cosh ((yoshidaEndpointA / 2) * x) * 1) =
        fun x ↦ Real.cosh (yoshidaEndpointA * x / 2) by
      funext x
      simp only [mul_one]
      congr 1
      ring]
    exact two_lt_integral_yoshidaEndpoint_cosh
  have hhead : (4 / 3 : ℝ) <
      yoshidaEndpointA * Real.exp yoshidaEndpointA * C ^ 2 := by
    have hexp : 1 < Real.exp yoshidaEndpointA := Real.one_lt_exp_iff.mpr
      yoshidaEndpointA_pos
    have hCsq : (4 : ℝ) < C ^ 2 := by nlinarith
    calc
      (4 / 3 : ℝ) < yoshidaEndpointA * 1 * 4 := by nlinarith
      _ < yoshidaEndpointA * Real.exp yoshidaEndpointA * 4 := by
        gcongr
      _ < yoshidaEndpointA * Real.exp yoshidaEndpointA * C ^ 2 := by
        gcongr
  have hsqrt : Real.sqrt 2 < (3 / 2 : ℝ) := by
    have hsqrtSq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2]
  have halpha : (4 / 9 : ℝ) < Real.log 2 / Real.sqrt 2 := by
    have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    rw [lt_div_iff₀ hsqrtPos]
    have hlog := six_hundred_ninety_three_div_thousand_lt_log_two
    nlinarith
  have hbeta : 0 ≤ Real.log 3 / Real.sqrt 3 := by positivity
  have hbudget : (8 / 9 : ℝ) <
      factorTwoCoupledPrimeMassBudget
        (fun _ : ℝ ↦ 1) (0 : ℝ → ℝ) := by
    unfold factorTwoCoupledPrimeMassBudget
    norm_num
    nlinarith
  nlinarith

/-- The phase-independent domination premise used by
`factorTwoEndpointChannelPhase_nonneg_of_coupledRank_domination` is already
strictly reversed on the constant even profile.  Thus the positive rank
energy cannot be detached from the signed head--tail and retained-prime
cancellation in a sharp endpoint proof. -/
theorem constant_even_strictly_reverses_coupledRank_domination :
    factorTwoEndpointChannelCleanSum
        (fun _ : ℝ ↦ 1) (0 : ℝ → ℝ) <
      factorTwoCoupledRankEnergy
          (fun _ : ℝ ↦ 1) (0 : ℝ → ℝ) +
        factorTwoCoupledPrimeMassBudget
          (fun _ : ℝ ↦ 1) (0 : ℝ → ℝ) := by
  have hzero : yoshidaEndpointOddCleanQuadratic (0 : ℝ → ℝ) = 0 := by
    unfold yoshidaEndpointOddCleanQuadratic centeredRawLogEnergy
      yoshidaEndpointRegularQuadratic yoshidaEndpointHyperbolicQuadratic
    simp
  rw [factorTwoEndpointChannelCleanSum, hzero, add_zero]
  exact constant_clean_lt_eight_fifths.trans
    ((by norm_num : (8 / 5 : ℝ) < 20 / 9).trans
      twenty_ninths_lt_constant_rank_add_primeBudget)

end

end ArithmeticHodge.Analysis.YoshidaFactorTwoPhaseCoupledRankDominationObstruction
