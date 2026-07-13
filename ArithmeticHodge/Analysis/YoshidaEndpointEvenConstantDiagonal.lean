import ArithmeticHodge.Analysis.YoshidaEndpointCleanQuadratic
import ArithmeticHodge.Analysis.YoshidaEndpointOddSharpMassLoss
import ArithmeticHodge.Analysis.YoshidaEndpointPotentialIntegrable

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenConstantDiagonal

open UnitIntervalLogEnergyAffine
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointPotentialIntegrable
open YoshidaRegularKernelSchur

noncomputable section

/-- Exact decomposition of the generic clean endpoint quadratic on the
constant even profile.  In particular, the logarithmic difference energy
vanishes, while the endpoint potential, regular kernel, and hyperbolic
rank-one term remain in their structural integral forms. -/
theorem yoshidaEndpointOddCleanQuadratic_one_eq :
    yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 1) =
      (∫ x : ℝ in -1..1, yoshidaEndpointPotential x) -
      2 * yoshidaEndpointScalarMassLoss -
      yoshidaEndpointA *
        (yoshidaEndpointRegularQuadratic (fun _ : ℝ ↦ (1 : ℂ))).re +
      yoshidaEndpointHyperbolicQuadratic (fun _ : ℝ ↦ (1 : ℂ)) := by
  unfold yoshidaEndpointOddCleanQuadratic centeredRawLogEnergy
  norm_num
  ring

/-- The first two positive terms of `-log (1-x²)` already give a fully
structural rational lower bound for the constant endpoint potential. -/
theorem thirteen_thirtieth_le_integral_endpointPotential :
    (13 / 30 : ℝ) ≤ ∫ x : ℝ in -1..1, yoshidaEndpointPotential x := by
  have hquartic : IntervalIntegrable yoshidaEndpointQuartic volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    unfold yoshidaEndpointQuartic
    fun_prop
  have hpotential : IntervalIntegrable yoshidaEndpointPotential volume (-1) 1 := by
    simpa only [one_pow, mul_one] using
      intervalIntegrable_endpointPotential_mul_sq (fun _ : ℝ ↦ 1) continuous_const
  have hmono :
      (∫ x : ℝ in -1..1, yoshidaEndpointQuartic x) ≤
        ∫ x : ℝ in -1..1, yoshidaEndpointPotential x := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      (by norm_num : (-1 : ℝ) ≤ 1) hquartic hpotential
    intro x hx
    apply quartic_le_endpointPotential
    rw [abs_lt]
    exact hx
  have hquarticExact :
      (∫ x : ℝ in -1..1, yoshidaEndpointQuartic x) = 13 / 30 := by
    unfold yoshidaEndpointQuartic
    norm_num
  linarith

/-- On the constant even profile the odd hyperbolic moment vanishes, while
`cosh ≥ 1`; hence the retained rank-one term contributes at least
`4 log 2`. -/
theorem four_mul_log_two_le_yoshidaEndpointHyperbolicQuadratic_one :
    4 * Real.log 2 ≤
      yoshidaEndpointHyperbolicQuadratic (fun _ : ℝ ↦ (1 : ℂ)) := by
  let C : ℝ := ∫ x : ℝ in -1..1,
    Real.cosh (yoshidaEndpointA * x / 2)
  let S : ℝ := ∫ x : ℝ in -1..1,
    Real.sinh (yoshidaEndpointA * x / 2)
  have hCint : IntervalIntegrable
      (fun x : ℝ ↦ Real.cosh (yoshidaEndpointA * x / 2)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hC : 2 ≤ C := by
    dsimp only [C]
    have h := intervalIntegral.integral_mono_on
      (by norm_num : (-1 : ℝ) ≤ 1)
      (Continuous.intervalIntegrable continuous_const (-1) 1) hCint
      (fun x _hx ↦ Real.one_le_cosh (yoshidaEndpointA * x / 2))
    norm_num at h ⊢
    exact h
  have hSodd : Function.Odd
      (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2)) := by
    intro x
    change Real.sinh (yoshidaEndpointA * (-x) / 2) =
      -Real.sinh (yoshidaEndpointA * x / 2)
    rw [show yoshidaEndpointA * -x / 2 =
      -(yoshidaEndpointA * x / 2) by ring, Real.sinh_neg]
  have hS : S = 0 := by
    dsimp only [S]
    have hchange := intervalIntegral.integral_comp_neg
      (f := fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * x / 2))
      (a := (-1 : ℝ)) (b := 1)
    have hneg :
        (∫ x : ℝ in -1..1, Real.sinh (yoshidaEndpointA * -x / 2)) =
          -(∫ x : ℝ in -1..1,
            Real.sinh (yoshidaEndpointA * x / 2)) := by
      rw [show (fun x : ℝ ↦ Real.sinh (yoshidaEndpointA * -x / 2)) =
          fun x ↦ -Real.sinh (yoshidaEndpointA * x / 2) by
        funext x
        exact hSodd x,
        intervalIntegral.integral_neg]
    norm_num only [neg_neg] at hchange
    rw [hneg] at hchange
    linarith
  have hCcomplex :
      (∫ x : ℝ in -1..1,
          (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (1 : ℂ)) =
        (C : ℂ) := by
    dsimp only [C]
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    norm_num
  have hScomplex :
      (∫ x : ℝ in -1..1,
          (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (1 : ℂ)) =
        (S : ℂ) := by
    dsimp only [S]
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    norm_num
  have hCsq : 4 ≤ C * C := by nlinarith
  unfold yoshidaEndpointHyperbolicQuadratic
  rw [hCcomplex, hScomplex, hS, Complex.normSq_ofReal]
  simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero, sub_zero]
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold yoshidaEndpointA
  nlinarith

/-- The regular remainder can cost at most `a` on the constant profile. -/
theorem neg_yoshidaEndpointA_mul_regular_one_lower :
    -(1733 / 5000 : ℝ) <
      -yoshidaEndpointA *
        (yoshidaEndpointRegularQuadratic (fun _ : ℝ ↦ (1 : ℂ))).re := by
  have hnorm := norm_yoshidaEndpointRegularQuadratic_le
    (fun _ : ℝ ↦ (1 : ℂ)) continuous_const
  norm_num at hnorm
  have hre :
      (yoshidaEndpointRegularQuadratic (fun _ : ℝ ↦ (1 : ℂ))).re ≤ 1 :=
    (re_le_norm _).trans hnorm
  have ha :=
    log_two_lt_one_thousand_seven_hundred_thirty_three_div_two_thousand_five_hundred
  have ha0 := yoshidaEndpointA_pos.le
  have hscaled := mul_le_mul_of_nonneg_left hre ha0
  unfold yoshidaEndpointA
  unfold yoshidaEndpointA at hscaled
  nlinarith

/-- The constant diagonal is not an obstruction: all analytic pieces are
kept, and transparent fixed bounds leave a strict rational margin. -/
theorem yoshidaEndpointOddCleanQuadratic_one_gt :
    (2171 / 15000 : ℝ) <
      yoshidaEndpointOddCleanQuadratic (fun _ : ℝ ↦ 1) := by
  have hpotential := thirteen_thirtieth_le_integral_endpointPotential
  have hregular := neg_yoshidaEndpointA_mul_regular_one_lower
  have hhyperbolic :=
    four_mul_log_two_le_yoshidaEndpointHyperbolicQuadratic_one
  have hgamma :=
    eulerMascheroniConstant_lt_two_hundred_eighty_nine_div_five_hundred
  have hlog := log_pi_mul_log_two_lt_seven_hundred_seventy_nine_div_thousand
  have hlogTwo := six_hundred_ninety_three_div_thousand_lt_log_two
  rw [yoshidaEndpointOddCleanQuadratic_one_eq]
  unfold yoshidaEndpointScalarMassLoss
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenConstantDiagonal
