import ArithmeticHodge.Analysis.YoshidaEndpointEvenStructuralReduction
import ArithmeticHodge.Analysis.YoshidaEndpointCleanQuadratic
import ArithmeticHodge.Analysis.YoshidaEndpointOddSharpMassLoss
import ArithmeticHodge.Analysis.YoshidaRegularKernelSharpMeanZeroSchur

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroPositive

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaRegularKernelSchur
open YoshidaRegularKernelSharpMeanZeroSchur

noncomputable section

/-- The endpoint hyperbolic term is nonnegative on a real even profile. -/
theorem yoshidaEndpointHyperbolicQuadratic_nonneg_of_even
    (w : ℝ → ℝ) (hweven : Function.Even w) :
    0 ≤ yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) := by
  let S : ℝ → ℂ := fun x ↦
    (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)
  have hSodd : Function.Odd S := by
    intro x
    dsimp only [S]
    rw [show yoshidaEndpointA * -x / 2 =
      -(yoshidaEndpointA * x / 2) by ring, Real.sinh_neg, hweven x]
    push_cast
    ring
  have hchange : (∫ x : ℝ in -1..1, S (-x)) =
      ∫ x : ℝ in -1..1, S x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := S)
        (a := (-1 : ℝ)) (b := 1))
  have hneg : (∫ x : ℝ in -1..1, S (-x)) =
      -(∫ x : ℝ in -1..1, S x) := by
    rw [show (fun x : ℝ ↦ S (-x)) = fun x ↦ -S x by
      funext x
      exact hSodd x]
    exact intervalIntegral.integral_neg
  have hzero : (∫ x : ℝ in -1..1, S x) = 0 := by
    rw [hneg] at hchange
    exact CharZero.neg_eq_self_iff.mp hchange
  unfold yoshidaEndpointHyperbolicQuadratic
  change 0 ≤ 2 * yoshidaEndpointA *
    (Complex.normSq _ - Complex.normSq (∫ x : ℝ in -1..1, S x))
  rw [hzero]
  simp only [Complex.normSq_zero, sub_zero]
  exact mul_nonneg
    (mul_nonneg (by norm_num) yoshidaEndpointA_pos.le)
    (Complex.normSq_nonneg _)

theorem yoshidaEndpointPotential_nonneg_on_Icc
    {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    0 ≤ yoshidaEndpointPotential x := by
  have hprod : 0 ≤ (x + 1) * (1 - x) :=
    mul_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  have harg0 : 0 ≤ 1 - x ^ 2 := by nlinarith
  have harg1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hlog := Real.log_nonpos harg0 harg1
  unfold yoshidaEndpointPotential
  linarith

theorem yoshidaEndpointEvenSharpMassLoss_lt_seven_fifths :
    yoshidaEndpointEvenSharpMassLoss < 7 / 5 := by
  have hgamma :=
    eulerMascheroniConstant_lt_two_hundred_eighty_nine_div_five_hundred
  have hlog :=
    log_pi_mul_log_two_lt_seven_hundred_seventy_nine_div_thousand
  have htwo :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred
  unfold yoshidaEndpointEvenSharpMassLoss
  linarith

/-- The complete clean endpoint quadratic is nonnegative on the mean-zero
even sector.  Only the fixed `P₂` mode and the genuinely infinite degree-four
tail enter the proof. -/
theorem yoshidaEndpointOddCleanQuadratic_nonneg_of_even_of_mean_zero
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hweven : Function.Even w)
    (hmean : centeredEvenP0Coefficient w = 0) :
    0 ≤ yoshidaEndpointOddCleanQuadratic w := by
  let f : ℝ → ℂ := fun x ↦ w x
  let b : ℝ := centeredEvenP2Coefficient w
  let r : ℝ → ℝ := centeredEvenZeroTwoResidual w
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let R : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  have hmass : 0 ≤ M := by
    dsimp only [M]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    exact sq_nonneg _
  have hresidualNonneg : 0 ≤ R := by
    dsimp only [R]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    exact sq_nonneg _
  have hresidualMass := integral_centeredEvenZeroTwoResidual_sq w hwcont
  have hmassDecomp : M = (2 / 5 : ℝ) * b ^ 2 + R := by
    dsimp only [M, R, r, b]
    rw [hmean] at hresidualMass
    norm_num at hresidualMass
    linarith
  have hreduction := centered_even_zero_two_tail_energy_le
    w hwcont hf henergy hweven
  have hcoercive : (7 / 5 : ℝ) * M ≤ centeredRawLogEnergy w / 4 := by
    calc
      (7 / 5 : ℝ) * M =
          (7 / 5 : ℝ) * ((2 / 5 : ℝ) * b ^ 2 + R) := by
        rw [hmassDecomp]
      _ ≤ (3 / 5 : ℝ) * b ^ 2 + (25 / 12 : ℝ) * R := by
        nlinarith [sq_nonneg b, hresidualNonneg]
      _ ≤ centeredRawLogEnergy w / 4 := by
        simpa only [b, R, r] using hreduction
  have hpotentialNonneg :
      0 ≤ ∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    apply mul_nonneg
    · apply yoshidaEndpointPotential_nonneg_on_Icc
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
    · exact sq_nonneg _
  have hloss : yoshidaEndpointEvenSharpMassLoss * M ≤
      centeredRawLogEnergy w / 4 +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) := by
    have hscaled := mul_le_mul_of_nonneg_right
      (le_of_lt yoshidaEndpointEvenSharpMassLoss_lt_seven_fifths) hmass
    linarith
  have hfcont : Continuous f := Complex.continuous_ofReal.comp hwcont
  have hmeanR : (∫ x : ℝ in -1..1, w x) = 0 := by
    unfold centeredEvenP0Coefficient at hmean
    linarith
  have hmeanInterval : (∫ x : ℝ in -1..1, f x) = 0 := by
    calc
      (∫ x : ℝ in -1..1, f x) =
          ((∫ x : ℝ in -1..1, w x : ℝ) : ℂ) :=
        intervalIntegral.integral_ofReal
      _ = 0 := by rw [hmeanR]; norm_num
  have hmeanSet : (∫ x : ℝ in Icc (-1) 1, f x) = 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hmeanInterval
  have hmassSet :
      (∫ x : ℝ in Icc (-1) 1, ‖f x‖ ^ 2) = M := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    dsimp only [M, f]
    apply intervalIntegral.integral_congr
    intro x _hx
    simp only [norm_real, Real.norm_eq_abs, sq_abs]
  have hregularNorm :=
    norm_yoshidaEndpointRegularQuadratic_le_one_thirty_second_of_integral_eq_zero
      f hfcont hmeanSet
  rw [hmassSet] at hregularNorm
  have hregularRe : (yoshidaEndpointRegularQuadratic f).re ≤
      ‖yoshidaEndpointRegularQuadratic f‖ := re_le_norm _
  have hregularLower :
      -(Real.log 2 / 64) * M ≤
        -yoshidaEndpointA * (yoshidaEndpointRegularQuadratic f).re := by
    have hscaledRe := mul_le_mul_of_nonneg_left hregularRe
      yoshidaEndpointA_pos.le
    have hscaledNorm := mul_le_mul_of_nonneg_left hregularNorm
      yoshidaEndpointA_pos.le
    have hscale : yoshidaEndpointA * ((1 / 32 : ℝ) * M) =
        (Real.log 2 / 64) * M := by
      unfold yoshidaEndpointA
      ring
    rw [hscale] at hscaledNorm
    linarith
  have hhyperbolic :=
    yoshidaEndpointHyperbolicQuadratic_nonneg_of_even w hweven
  unfold yoshidaEndpointOddCleanQuadratic
  unfold yoshidaEndpointEvenSharpMassLoss at hloss
  unfold yoshidaEndpointScalarMassLoss
  dsimp only [M, f] at hloss hregularLower ⊢
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroPositive
