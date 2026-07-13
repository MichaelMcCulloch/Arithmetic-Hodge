import ArithmeticHodge.Analysis.UnitIntervalLogEnergyLipschitz
import ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroReserve
import ArithmeticHodge.Analysis.YoshidaEndpointPullbackLipschitz

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroLocallyLipschitz

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointEvenMeanZeroReserve
open YoshidaEndpointEvenStructuralReduction
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointPullbackLipschitz

noncomputable section

/-- The quantitative mean-zero even reserve needs no separate form-domain
hypotheses for locally Lipschitz centered profiles. -/
theorem yoshidaEndpointOddCleanQuadratic_reserve_of_even_of_mean_zero_of_locallyLipschitzOn
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hweven : Function.Even w)
    (hmean : centeredEvenP0Coefficient w = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w) :
    (1 / 25 : ℝ) * centeredEvenP2Coefficient w ^ 2 +
        (41 / 60 : ℝ) *
          (∫ x : ℝ in -1..1, centeredEvenZeroTwoResidual w x ^ 2) ≤
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
    yoshidaEndpointOddCleanQuadratic_reserve_of_even_of_mean_zero
      w hwcont (by simpa only [f] using hfmem)
        (by simpa only [f] using henergy) hweven hmean

/-- In particular, every locally Lipschitz real even mean-zero centered
profile has nonnegative clean endpoint energy. -/
theorem yoshidaEndpointOddCleanQuadratic_nonneg_of_even_of_mean_zero_of_locallyLipschitzOn
    (w : ℝ → ℝ) (hwcont : Continuous w)
    (hweven : Function.Even w)
    (hmean : centeredEvenP0Coefficient w = 0)
    (hlocal : LocallyLipschitzOn (Icc (-1) 1) w) :
    0 ≤ yoshidaEndpointOddCleanQuadratic w := by
  have hreserve :=
    yoshidaEndpointOddCleanQuadratic_reserve_of_even_of_mean_zero_of_locallyLipschitzOn
      w hwcont hweven hmean hlocal
  have htail : 0 ≤
      ∫ x : ℝ in -1..1, centeredEvenZeroTwoResidual w x ^ 2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _hx
    exact sq_nonneg _
  nlinarith [sq_nonneg (centeredEvenP2Coefficient w)]

end


end ArithmeticHodge.Analysis.YoshidaEndpointEvenMeanZeroLocallyLipschitz
