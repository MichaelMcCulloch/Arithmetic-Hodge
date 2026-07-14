import ArithmeticHodge.Analysis.YoshidaEndpointOcticOddCoercivity

set_option autoImplicit false

open MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointOddResidualRegularity

noncomputable section

open CenteredOddOneThreeEnergy
open YoshidaEndpointOcticOddCoercivity
open YoshidaEndpointOcticPotential

/-!
# Regularity of the structural odd one-three residual

The odd endpoint profile is decomposed into its two intrinsic Legendre modes
`P₁,P₃` and the genuine infinite-dimensional residual.  No Fourier cutoff
or finite-mode approximation enters these lemmas.
-/

/-- The intrinsic two-dimensional odd low profile. -/
def factorTwoOddStructuralLowProfile (c d : ℝ) : ℝ → ℝ := fun x ↦
  c * centeredP1 x + d * centeredP3 x

theorem continuous_factorTwoOddStructuralLowProfile (c d : ℝ) :
    Continuous (factorTwoOddStructuralLowProfile c d) := by
  unfold factorTwoOddStructuralLowProfile centeredP1 centeredP3
  fun_prop

theorem odd_factorTwoOddStructuralLowProfile (c d : ℝ) :
    Function.Odd (factorTwoOddStructuralLowProfile c d) := by
  intro x
  unfold factorTwoOddStructuralLowProfile centeredP1 centeredP3
  ring

theorem continuous_centeredOddOneThreeResidual
    (w : ℝ → ℝ) (hw : Continuous w) :
    Continuous (centeredOddOneThreeResidual w) := by
  unfold centeredOddOneThreeResidual centeredP1 centeredP3
  fun_prop

theorem odd_centeredOddOneThreeResidual
    (w : ℝ → ℝ) (hw : Function.Odd w) :
    Function.Odd (centeredOddOneThreeResidual w) := by
  intro x
  unfold centeredOddOneThreeResidual centeredP1 centeredP3
  rw [hw]
  ring

theorem centeredOddP1Coefficient_oneThreeResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredOddP1Coefficient (centeredOddOneThreeResidual w) = 0 := by
  have h := integral_centeredOddResidual_mul_p1 w hw
  unfold centeredOddP1Coefficient
  rw [h]
  ring

theorem centeredOddP3Coefficient_oneThreeResidual_eq_zero
    (w : ℝ → ℝ) (hw : Continuous w) :
    centeredOddP3Coefficient (centeredOddOneThreeResidual w) = 0 := by
  have h := integral_centeredOddResidual_mul_p3 w hw
  unfold centeredOddP3Coefficient
  rw [h]
  ring

theorem locallyLipschitzOn_centeredOddOneThreeResidual
    (w : ℝ → ℝ)
    (hw : LocallyLipschitzOn (Icc (-1) 1) w) :
    LocallyLipschitzOn (Icc (-1) 1)
      (centeredOddOneThreeResidual w) := by
  have hlowDiff : ContDiffOn ℝ 1
      (factorTwoOddStructuralLowProfile
        (centeredOddP1Coefficient w) (centeredOddP3Coefficient w))
      (Icc (-1) 1) := by
    unfold factorTwoOddStructuralLowProfile centeredP1 centeredP3
    fun_prop
  have hlow := hlowDiff.locallyLipschitzOn (convex_Icc (-1) 1)
  rw [show centeredOddOneThreeResidual w = fun x ↦
      w x - factorTwoOddStructuralLowProfile
        (centeredOddP1Coefficient w) (centeredOddP3Coefficient w) x by
    funext x
    unfold centeredOddOneThreeResidual factorTwoOddStructuralLowProfile
    ring]
  exact hw.sub hlow

/-- Exact reconstruction from the two intrinsic odd modes and the residual. -/
theorem oddLow_add_oneThreeResidual_eq (w : ℝ → ℝ) :
    factorTwoOddStructuralLowProfile
          (centeredOddP1Coefficient w) (centeredOddP3Coefficient w) +
        centeredOddOneThreeResidual w =
      w := by
  funext x
  unfold factorTwoOddStructuralLowProfile centeredOddOneThreeResidual
  simp only [Pi.add_apply]
  ring

end

end ArithmeticHodge.Analysis.YoshidaEndpointOddResidualRegularity
