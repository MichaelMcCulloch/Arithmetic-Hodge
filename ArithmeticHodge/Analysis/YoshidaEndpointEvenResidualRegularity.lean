import ArithmeticHodge.Analysis.YoshidaEndpointEvenFullPolarization

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualRegularity

open YoshidaEndpointEvenStructuralReduction

noncomputable section

/-!
# Regularity of the structural even zero-two residual

These lemmas package the exact infinite-dimensional decomposition used by
the final even Schur argument.  They remove only the two fixed Legendre
modes and make no finite-mode approximation.
-/

theorem continuous_centeredEvenZeroTwoResidual
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (centeredEvenZeroTwoResidual w) := by
  unfold centeredEvenZeroTwoResidual centeredEvenP0 centeredEvenP2
  fun_prop

theorem centeredEvenP0Coefficient_zeroTwoResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredEvenP0Coefficient (centeredEvenZeroTwoResidual w) = 0 := by
  have h := integral_centeredEvenResidual_mul_p0 w hw
  rw [integral_mul_centeredEvenP0_eq] at h
  linarith

theorem centeredEvenP2Coefficient_zeroTwoResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredEvenP2Coefficient (centeredEvenZeroTwoResidual w) = 0 := by
  have h := integral_centeredEvenResidual_mul_p2 w hw
  rw [integral_mul_centeredEvenP2_eq] at h
  linarith

theorem locallyLipschitzOn_centeredEvenZeroTwoResidual
    (w : ℝ → ℝ)
    (hw : LocallyLipschitzOn (Icc (-1) 1) w) :
    LocallyLipschitzOn (Icc (-1) 1) (centeredEvenZeroTwoResidual w) := by
  have hlowDiff : ContDiffOn ℝ 1
      (fun x : ℝ ↦
        centeredEvenP0Coefficient w * centeredEvenP0 x +
          centeredEvenP2Coefficient w * centeredEvenP2 x)
      (Icc (-1) 1) := by
    unfold centeredEvenP0 centeredEvenP2
    fun_prop
  have hlow := hlowDiff.locallyLipschitzOn (convex_Icc (-1) 1)
  rw [show centeredEvenZeroTwoResidual w = fun x ↦
      w x - (centeredEvenP0Coefficient w * centeredEvenP0 x +
        centeredEvenP2Coefficient w * centeredEvenP2 x) by
    funext x
    unfold centeredEvenZeroTwoResidual
    ring]
  exact hw.sub hlow

theorem low_add_zeroTwoResidual_eq (w : ℝ → ℝ) :
    (fun x ↦
      centeredEvenP0Coefficient w * centeredEvenP0 x +
        centeredEvenP2Coefficient w * centeredEvenP2 x +
        centeredEvenZeroTwoResidual w x) = w := by
  funext x
  unfold centeredEvenZeroTwoResidual
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointEvenResidualRegularity
