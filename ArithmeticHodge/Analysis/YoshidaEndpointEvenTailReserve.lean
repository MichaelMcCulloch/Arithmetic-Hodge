import ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroLocallyLipschitz

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenTailReserve

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenMeanZeroPositive
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointOddSharpMassLoss
open YoshidaEndpointPotentialBound
open YoshidaEndpointPullbackLipschitz
open YoshidaRegularKernelSchur
open YoshidaRegularKernelSharpMeanZeroSchur

noncomputable section

/-- The mean-zero even reserve with the positive endpoint potential and
hyperbolic forms retained. -/
theorem yoshidaEndpointOddCleanQuadratic_tail_reserve_of_even_of_mean_zero
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hf : MemLp (fun t : unitInterval ↦ centeredPullback w (t : ℝ)) 2)
    (henergy : Integrable (unitIntervalRawLogEnergyIntegrand
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))))
    (hweven : Function.Even w)
    (hmean : centeredEvenP0Coefficient w = 0) :
    (1 / 25 : ℝ) * centeredEvenP2Coefficient w ^ 2 +
        (41 / 60 : ℝ) *
          (∫ x : ℝ in -1..1, centeredEvenZeroTwoResidual w x ^ 2) +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) +
        yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) ≤
      yoshidaEndpointOddCleanQuadratic w := by
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
  have hresidualMass := integral_centeredEvenZeroTwoResidual_sq w hwcont
  have hmassDecomp : M = (2 / 5 : ℝ) * b ^ 2 + R := by
    dsimp only [M, R, r, b]
    rw [hmean] at hresidualMass
    norm_num at hresidualMass
    linarith
  have hreduction := centered_even_zero_two_tail_energy_le
    w hwcont hf henergy hweven
  have hcoerciveReserve :
      (1 / 25 : ℝ) * b ^ 2 + (41 / 60 : ℝ) * R +
          (7 / 5 : ℝ) * M ≤
        centeredRawLogEnergy w / 4 := by
    calc
      (1 / 25 : ℝ) * b ^ 2 + (41 / 60 : ℝ) * R +
          (7 / 5 : ℝ) * M =
          (3 / 5 : ℝ) * b ^ 2 + (25 / 12 : ℝ) * R := by
        rw [hmassDecomp]
        ring
      _ ≤ centeredRawLogEnergy w / 4 := by
        simpa only [b, R, r] using hreduction
  have hlossReserve :
      (1 / 25 : ℝ) * b ^ 2 + (41 / 60 : ℝ) * R +
          yoshidaEndpointEvenSharpMassLoss * M ≤
        centeredRawLogEnergy w / 4 := by
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
          (((∫ x : ℝ in -1..1, w x) : ℝ) : ℂ) :=
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
  unfold yoshidaEndpointOddCleanQuadratic
  unfold yoshidaEndpointEvenSharpMassLoss at hlossReserve
  unfold yoshidaEndpointScalarMassLoss
  dsimp only [M, R, r, b, f] at hlossReserve hregularLower ⊢
  linarith

/-- Local Lipschitz regularity on the centered compact interval supplies all
form-domain hypotheses of the retained mean-zero even reserve. -/
theorem yoshidaEndpointOddCleanQuadratic_tail_reserve_of_even_of_mean_zero_of_locallyLipschitzOn
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hweven : Function.Even w)
    (hmean : centeredEvenP0Coefficient w = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w) :
    (1 / 25 : ℝ) * centeredEvenP2Coefficient w ^ 2 +
        (41 / 60 : ℝ) *
          (∫ x : ℝ in -1..1, centeredEvenZeroTwoResidual w x ^ 2) +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) +
        yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) ≤
      yoshidaEndpointOddCleanQuadratic w := by
  obtain ⟨C, hLip⟩ :=
    exists_lipschitzWith_centeredPullback w hlocal
  let f : unitInterval → ℝ := fun t ↦ centeredPullback w (t : ℝ)
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  exact
    yoshidaEndpointOddCleanQuadratic_tail_reserve_of_even_of_mean_zero
      w hwcont (by simpa only [f] using hfmem)
        (by simpa only [f] using henergy) hweven hmean

/-- On the literal even tail, the zero-two residual is the profile itself. -/
theorem yoshidaEndpointOddCleanQuadratic_tail_reserve_of_zero_two_of_locallyLipschitzOn
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hweven : Function.Even w)
    (hmean : centeredEvenP0Coefficient w = 0)
    (htwo : centeredEvenP2Coefficient w = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w) :
    (41 / 60 : ℝ) * (∫ x : ℝ in -1..1, w x ^ 2) +
        (∫ x : ℝ in -1..1, yoshidaEndpointPotential x * w x ^ 2) +
        yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) ≤
      yoshidaEndpointOddCleanQuadratic w := by
  have hreserve :=
    yoshidaEndpointOddCleanQuadratic_tail_reserve_of_even_of_mean_zero_of_locallyLipschitzOn
      w hwcont hweven hmean hlocal
  have hresidual : centeredEvenZeroTwoResidual w = w := by
    funext x
    unfold centeredEvenZeroTwoResidual
    rw [hmean, htwo]
    ring
  rw [hresidual, htwo] at hreserve
  norm_num at hreserve
  exact hreserve

end
end ArithmeticHodge.Analysis.YoshidaEndpointEvenTailReserve
