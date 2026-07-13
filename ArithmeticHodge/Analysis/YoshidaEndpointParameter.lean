import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

namespace ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound

noncomputable section

/-!
# The fixed Yoshida endpoint parameter

This lightweight module isolates the endpoint half-width from the analytic
estimates that consume it.  Structural support-transport modules can therefore
name the exact endpoint without importing any spectral certificate layer.
-/

/-- The endpoint half-width in the scaled Yoshida form. -/
def yoshidaEndpointA : ℝ := Real.log 2 / 2

theorem yoshidaEndpointA_pos : 0 < yoshidaEndpointA := by
  unfold yoshidaEndpointA
  positivity

end

end ArithmeticHodge.Analysis.YoshidaEndpointHyperbolicBound
