import ArithmeticHodge.Analysis.UnitIntervalLogEnergyLipschitz
import ArithmeticHodge.Analysis.YoshidaEndpointOddCleanContinuous
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false

open MeasureTheory

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddCleanLipschitz

open UnitIntervalLogEnergyAffine
open UnitIntervalLogEnergyLipschitz
open UnitIntervalLogEnergyProjection
open YoshidaEndpointOddCleanContinuous
open YoshidaEndpointOddCleanPositive

noncomputable section

/-- A continuous odd profile whose centered pullback is Lipschitz satisfies
the complete clean endpoint inequality with no separate form-domain premise. -/
theorem yoshidaEndpointOddCleanQuadratic_nonneg_of_lipschitzWith
    (w : ℝ → ℝ) (hwcont : Continuous w) (hwodd : Function.Odd w)
    {C : NNReal}
    (hLip : LipschitzWith C
      (fun t : unitInterval ↦ centeredPullback w (t : ℝ))) :
    0 ≤ yoshidaEndpointOddCleanQuadratic w := by
  let f : unitInterval → ℝ :=
    fun t ↦ centeredPullback w (t : ℝ)
  have hfcont : Continuous f := by
    dsimp only [f, centeredPullback]
    fun_prop
  have hfmem : MemLp f 2 :=
    hfcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have henergy : Integrable (unitIntervalRawLogEnergyIntegrand f) :=
    integrable_unitIntervalRawLogEnergyIntegrand_of_lipschitzWith f
      (by simpa only [f] using hLip)
  exact yoshidaEndpointOddCleanQuadratic_nonneg_of_continuous
    w hwcont (by simpa only [f] using hfmem)
      (by simpa only [f] using henergy) hwodd

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddCleanLipschitz
