import ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound
import ArithmeticHodge.Analysis.YoshidaEndpointCleanQuadratic
import ArithmeticHodge.Analysis.YoshidaEndpointOddCorePositive
import ArithmeticHodge.Analysis.YoshidaRegularKernelSharpMeanZeroSchur

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddCleanPositive

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCorePositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaRegularKernelSchur
open YoshidaRegularKernelSharpMeanZeroSchur

noncomputable section

theorem yoshidaEndpointOddCleanQuadratic_nonneg
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hwodd : Function.Odd w)
    (hpotential : IntervalIntegrable
      (fun x ↦ yoshidaEndpointPotential x * w x ^ 2) volume (-1) 1) :
    0 ≤ yoshidaEndpointOddCleanQuadratic w := by
  let f : ℝ → ℂ := fun x ↦ w x
  have hfcont : Continuous f := by
    exact Complex.continuous_ofReal.comp hwcont
  have hfodd : Function.Odd f := by
    intro x
    change (w (-x) : ℂ) = -(w x : ℂ)
    rw [hwodd x]
    norm_num
  have hmeanInterval : (∫ x : ℝ in -1..1, f x) = 0 := by
    have hchange :
        (∫ x : ℝ in -1..1, f (-x)) = ∫ x : ℝ in -1..1, f x := by
      simpa only [neg_neg] using
        (intervalIntegral.integral_comp_neg (f := f) (a := (-1 : ℝ)) (b := 1))
    have hoddIntegral :
        (∫ x : ℝ in -1..1, f (-x)) = -∫ x : ℝ in -1..1, f x := by
      rw [show (fun x : ℝ ↦ f (-x)) = fun x ↦ -f x by
        funext x
        exact hfodd x]
      exact intervalIntegral.integral_neg
    rw [hoddIntegral] at hchange
    exact CharZero.neg_eq_self_iff.mp hchange
  have hmean : (∫ x : ℝ in Icc (-1) 1, f x) = 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hmeanInterval
  have hnormSq (x : ℝ) : ‖f x‖ ^ 2 = w x ^ 2 := by
    simp only [f, norm_real, Real.norm_eq_abs, sq_abs]
  have hmassSet :
      (∫ x : ℝ in Icc (-1) 1, ‖f x‖ ^ 2) =
        ∫ x : ℝ in -1..1, w x ^ 2 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    apply intervalIntegral.integral_congr
    intro x _hx
    exact hnormSq x
  have hmassInterval :
      (∫ x : ℝ in -1..1, ‖f x‖ ^ 2) =
        ∫ x : ℝ in -1..1, w x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _hx
    exact hnormSq x
  have hregularNorm :=
    norm_yoshidaEndpointRegularQuadratic_le_one_thirty_second_of_integral_eq_zero
      f hfcont hmean
  rw [hmassSet] at hregularNorm
  have hregularRe :
      (yoshidaEndpointRegularQuadratic f).re ≤
        ‖yoshidaEndpointRegularQuadratic f‖ :=
    re_le_norm _
  have hregularLower :
      -(Real.log 2 / 64) * (∫ x : ℝ in -1..1, w x ^ 2) ≤
        -yoshidaEndpointA * (yoshidaEndpointRegularQuadratic f).re := by
    have ha : 0 ≤ yoshidaEndpointA := yoshidaEndpointA_pos.le
    have hreScaled :
        yoshidaEndpointA * (yoshidaEndpointRegularQuadratic f).re ≤
          yoshidaEndpointA * ‖yoshidaEndpointRegularQuadratic f‖ :=
      mul_le_mul_of_nonneg_left hregularRe ha
    have hnormScaled :
        yoshidaEndpointA * ‖yoshidaEndpointRegularQuadratic f‖ ≤
          yoshidaEndpointA *
            ((1 / 32 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2) :=
      mul_le_mul_of_nonneg_left hregularNorm ha
    have hscale :
        yoshidaEndpointA *
            ((1 / 32 : ℝ) * ∫ x : ℝ in -1..1, w x ^ 2) =
          (Real.log 2 / 64) * ∫ x : ℝ in -1..1, w x ^ 2 := by
      unfold yoshidaEndpointA
      ring
    rw [hscale] at hnormScaled
    linarith
  have hhyperbolic := yoshidaEndpointHyperbolicQuadratic_lower f hfcont
  rw [hmassInterval] at hhyperbolic
  have hcore := yoshidaEndpointOddCoreQuadratic_nonneg
    w hwcont hf henergy hwodd hpotential
  dsimp only [yoshidaEndpointOddCleanQuadratic]
  unfold yoshidaEndpointOddCoreQuadratic at hcore
  unfold yoshidaEndpointOddSharpMassLoss yoshidaEndpointEvenSharpMassLoss at hcore
  unfold yoshidaEndpointScalarMassLoss
  change _ + _ - _ - yoshidaEndpointA *
      (yoshidaEndpointRegularQuadratic f).re +
      yoshidaEndpointHyperbolicQuadratic f ≥ 0
  linarith

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddCleanPositive
