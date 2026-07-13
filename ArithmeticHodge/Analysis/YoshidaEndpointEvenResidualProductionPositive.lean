import ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProduction

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProductionPositive

open ArithmeticHodge.Analysis
open YoshidaClippedEndpointContinuous
open YoshidaEndpointEvenBoundaryResidual
open YoshidaEndpointEvenResidualProduction
open YoshidaEndpointHyperbolicBound
open YoshidaEndpointOddCleanPositive
open YoshidaEndpointScaledCorrelation
open YoshidaPointwiseParityCore
open YoshidaSectionSixAnalytic

noncomputable section

/-!
# Production positivity of the zero-trace even boundary residual

This is the exact production-level consequence of complete clean-even
positivity.  Reconnecting the removed endpoint constant is a separate exact
boundary-bridge obligation; no positivity claim about the original full
source is made here.
-/

/-- Any theorem proving the clean endpoint quadratic nonnegative on the full
continuous even form domain proves the actual production diagonal
nonnegative on every real zero-trace even boundary residual. -/
theorem clippedCriticalFormValue_evenBoundaryResidual_nonneg_of_cleanEven
    (hclean : ∀ w : ℝ → ℝ, Continuous w → Function.Even w →
      LocallyLipschitzOn (Icc (-1) 1) w →
        0 ≤ yoshidaEndpointOddCleanQuadratic w)
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule yoshidaEndpointA)
    (hf_real : ∀ x : ℝ,
      ((((f.1 : YoshidaClippedPeriodicCore yoshidaEndpointA) :
        YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) x).im = 0) :
    0 ≤ clippedCriticalFormValue yoshidaEndpointA yoshidaEndpointA_pos
      (evenBoundaryResidual f : YoshidaClippedSmooth yoshidaEndpointA) := by
  let r : YoshidaClippedPeriodicCore yoshidaEndpointA :=
    evenBoundaryResidual f
  let g : ℝ → ℝ := fun x ↦
    ((r : YoshidaClippedSmooth yoshidaEndpointA) x).re
  let w : ℝ → ℝ := centeredRescale yoshidaEndpointA g
  have hends :
      ((r : YoshidaClippedSmooth yoshidaEndpointA) (-yoshidaEndpointA) = 0) ∧
      ((r : YoshidaClippedSmooth yoshidaEndpointA) yoshidaEndpointA = 0) := by
    simpa only [r] using
      evenBoundaryResidual_endpoints_zero yoshidaEndpointA_pos f
  have hrcont : Continuous
      ((r : YoshidaClippedSmooth yoshidaEndpointA) : ℝ → ℂ) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero
      yoshidaEndpointA_pos _ hends.1 hends.2
  have hgcont : Continuous g := Complex.continuous_re.comp hrcont
  have hgeven : Function.Even g := by
    intro x
    have heven := evenBoundaryResidual_pointwise_even f x
    exact congrArg Complex.re heven
  have hwcont : Continuous w := by
    dsimp only [w, centeredRescale]
    exact hgcont.comp (continuous_const.mul continuous_id)
  have hweven : Function.Even w := by
    intro x
    dsimp only [w, centeredRescale]
    rw [show yoshidaEndpointA * -x = -(yoshidaEndpointA * x) by ring,
      hgeven]
  have hprofile : ContDiffOn ℝ 1 g
      (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    exact Complex.reCLM.contDiff.comp_contDiffOn
      ((r : YoshidaClippedSmooth yoshidaEndpointA).property.1.of_le (by simp))
  have hscale : ContDiffOn ℝ 1
      (fun x : ℝ ↦ yoshidaEndpointA * x) (Icc (-1) 1) := by
    fun_prop
  have hmaps : MapsTo (fun x : ℝ ↦ yoshidaEndpointA * x)
      (Icc (-1) 1) (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    intro x hx
    constructor <;> nlinarith [hx.1, hx.2, yoshidaEndpointA_pos]
  have hlocal : LocallyLipschitzOn (Icc (-1) 1) w := by
    have hcomp := hprofile.comp hscale hmaps
    simpa only [w, centeredRescale, Function.comp_apply] using
      hcomp.locallyLipschitzOn (convex_Icc (-1) 1)
  have hQ : 0 ≤ yoshidaEndpointOddCleanQuadratic w :=
    hclean w hwcont hweven hlocal
  have hbridge :=
    clippedCriticalFormValue_evenBoundaryResidual_eq_clean f hf_real
  dsimp only [r, g, w] at hbridge ⊢
  rw [hbridge]
  exact mul_nonneg yoshidaEndpointA_pos.le hQ

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualProductionPositive
