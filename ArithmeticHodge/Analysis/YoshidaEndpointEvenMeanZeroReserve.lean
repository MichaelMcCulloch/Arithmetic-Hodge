import ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroPositive

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroReserve

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaRegularKernelSchur
open YoshidaRegularKernelSharpMeanZeroSchur

noncomputable section

/-- Exact structural reserve before replacing the endpoint mass-loss constant
by its rational upper bound. -/
theorem yoshidaEndpointOddCleanQuadratic_sharp_reserve_of_even_of_mean_zero
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hweven : Function.Even w)
    (hmean : centeredEvenP0Coefficient w = 0) :
    ((3 / 5 : ℝ) - (2 / 5 : ℝ) * yoshidaEndpointEvenSharpMassLoss) *
          centeredEvenP2Coefficient w ^ 2 +
        ((25 / 12 : ℝ) - yoshidaEndpointEvenSharpMassLoss) *
          (∫ x : ℝ in -1..1, centeredEvenZeroTwoResidual w x ^ 2) ≤
      yoshidaEndpointOddCleanQuadratic w := by
  let f : ℝ → ℂ := fun x ↦ w x
  let b : ℝ := centeredEvenP2Coefficient w
  let r : ℝ → ℝ := centeredEvenZeroTwoResidual w
  let M : ℝ := ∫ x : ℝ in -1..1, w x ^ 2
  let R : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  have hresidualMass := integral_centeredEvenZeroTwoResidual_sq w hwcont
  have hmassDecomp : M = (2 / 5 : ℝ) * b ^ 2 + R := by
    dsimp only [M, R, r, b]
    rw [hmean] at hresidualMass
    norm_num at hresidualMass
    linarith
  have hreduction := centered_even_zero_two_tail_energy_le
    w hwcont hf henergy hweven
  have hcoerciveReserve :
      ((3 / 5 : ℝ) - (2 / 5 : ℝ) * yoshidaEndpointEvenSharpMassLoss) *
            b ^ 2 +
          ((25 / 12 : ℝ) - yoshidaEndpointEvenSharpMassLoss) * R +
          yoshidaEndpointEvenSharpMassLoss * M ≤
        centeredRawLogEnergy w / 4 := by
    calc
      ((3 / 5 : ℝ) - (2 / 5 : ℝ) * yoshidaEndpointEvenSharpMassLoss) *
            b ^ 2 +
          ((25 / 12 : ℝ) - yoshidaEndpointEvenSharpMassLoss) * R +
          yoshidaEndpointEvenSharpMassLoss * M =
          (3 / 5 : ℝ) * b ^ 2 + (25 / 12 : ℝ) * R := by
        rw [hmassDecomp]
        ring
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
  have hlossReserve :
      ((3 / 5 : ℝ) - (2 / 5 : ℝ) * yoshidaEndpointEvenSharpMassLoss) *
            b ^ 2 +
          ((25 / 12 : ℝ) - yoshidaEndpointEvenSharpMassLoss) * R +
          yoshidaEndpointEvenSharpMassLoss * M ≤
        centeredRawLogEnergy w / 4 +
          (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) := by
    linarith
  have hfcont : Continuous f := Complex.continuous_ofReal.comp hwcont
  have hmeanR : (∫ x : ℝ in -1..1, w x) = 0 := by
    unfold centeredEvenP0Coefficient at hmean
    linarith
  have hmeanInterval : (∫ x : ℝ in -1..1, f x) = 0 := by
    calc
      (∫ x : ℝ in -1..1, f x) =
          (((∫ x : ℝ in -1..1, w x) : ℝ) : ℂ) :=
        intervalIntegral.integral_ofReal
      _ = 0 := by rw [hmeanR]; norm_num
  have hmeanSet : (∫ x : ℝ in Set.Icc (-1) 1, f x) = 0 := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hmeanInterval
  have hmassSet :
      (∫ x : ℝ in Set.Icc (-1) 1, ‖f x‖ ^ 2) = M := by
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
      ‖yoshidaEndpointRegularQuadratic f‖ := Complex.re_le_norm _
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
  unfold yoshidaEndpointEvenSharpMassLoss at hlossReserve ⊢
  unfold yoshidaEndpointScalarMassLoss
  dsimp only [M, R, r, b, f] at hlossReserve hregularLower ⊢
  linarith

/-- Quantitative coercivity of the clean endpoint quadratic on the mean-zero
even sector.  The two reserve coefficients are the exact remainder after the
structural `P₂`/even-tail logarithmic bounds absorb the rational mass loss
`7 / 5`. -/
theorem yoshidaEndpointOddCleanQuadratic_reserve_of_even_of_mean_zero
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hweven : Function.Even w)
    (hmean : centeredEvenP0Coefficient w = 0) :
    (1 / 25 : ℝ) * centeredEvenP2Coefficient w ^ 2 +
        (41 / 60 : ℝ) *
          (∫ x : ℝ in -1..1, centeredEvenZeroTwoResidual w x ^ 2) ≤
      yoshidaEndpointOddCleanQuadratic w := by
  let b : ℝ := centeredEvenP2Coefficient w
  let r : ℝ → ℝ := centeredEvenZeroTwoResidual w
  let R : ℝ := ∫ x : ℝ in -1..1, r x ^ 2
  have hresidualNonneg : 0 ≤ R := by
    dsimp only [R]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    exact sq_nonneg _
  have hsharp :=
    yoshidaEndpointOddCleanQuadratic_sharp_reserve_of_even_of_mean_zero
      w hwcont hf henergy hweven hmean
  have hloss : yoshidaEndpointEvenSharpMassLoss ≤ (7 / 5 : ℝ) :=
    le_of_lt yoshidaEndpointEvenSharpMassLoss_lt_seven_fifths
  have hdelta : 0 ≤ (7 / 5 : ℝ) - yoshidaEndpointEvenSharpMassLoss :=
    sub_nonneg.mpr hloss
  have hbGain : 0 ≤
      ((2 / 5 : ℝ) *
        ((7 / 5 : ℝ) - yoshidaEndpointEvenSharpMassLoss)) * b ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) hdelta) (sq_nonneg b)
  have hresidualGain : 0 ≤
      ((7 / 5 : ℝ) - yoshidaEndpointEvenSharpMassLoss) * R :=
    mul_nonneg hdelta hresidualNonneg
  calc
    (1 / 25 : ℝ) * centeredEvenP2Coefficient w ^ 2 +
        (41 / 60 : ℝ) *
          (∫ x : ℝ in -1..1, centeredEvenZeroTwoResidual w x ^ 2) ≤
      ((3 / 5 : ℝ) - (2 / 5 : ℝ) * yoshidaEndpointEvenSharpMassLoss) *
          centeredEvenP2Coefficient w ^ 2 +
        ((25 / 12 : ℝ) - yoshidaEndpointEvenSharpMassLoss) *
          (∫ x : ℝ in -1..1, centeredEvenZeroTwoResidual w x ^ 2) := by
      dsimp only [b, R, r] at hbGain hresidualGain
      linarith
    _ ≤ yoshidaEndpointOddCleanQuadratic w := hsharp

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroReserve
