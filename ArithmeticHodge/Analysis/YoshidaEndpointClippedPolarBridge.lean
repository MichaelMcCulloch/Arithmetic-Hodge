import ArithmeticHodge.Analysis.YoshidaEndpointPolarScaling
import ArithmeticHodge.Analysis.YoshidaSectionSixAnalytic

set_option autoImplicit false

open Complex MeasureTheory Real Set

namespace ArithmeticHodge.Analysis.YoshidaEndpointClippedPolarBridge

open YoshidaEndpointHyperbolicBound
open YoshidaEndpointPolarScaling
open YoshidaSectionSixAnalytic

noncomputable section

/-- For a real-valued clipped profile, the production polar energy is exactly
the endpoint hyperbolic quadratic of its centered real rescaling. -/
theorem clippedPolarEnergy_eq_endpointHyperbolicQuadratic
    (f : YoshidaClippedSmooth yoshidaEndpointA)
    (hf_real : ∀ y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA,
      f y = ((f y).re : ℂ)) :
    clippedPolarEnergy yoshidaEndpointA yoshidaEndpointA_pos f =
      yoshidaEndpointA *
        yoshidaEndpointHyperbolicQuadratic
          (fun x ↦ ((f (yoshidaEndpointA * x)).re : ℂ)) := by
  let w : ℝ → ℝ := fun x ↦ (f (yoshidaEndpointA * x)).re
  have hmap : MapsTo (fun x : ℝ ↦ yoshidaEndpointA * x)
      (Icc (-1) 1) (Icc (-yoshidaEndpointA) yoshidaEndpointA) := by
    intro x hx
    constructor
    · simpa using mul_le_mul_of_nonneg_left hx.1 yoshidaEndpointA_pos.le
    · simpa using mul_le_mul_of_nonneg_left hx.2 yoshidaEndpointA_pos.le
  have hwOn : ContinuousOn w (Icc (-1) 1) := by
    have hfOn : ContinuousOn
        (fun x : ℝ ↦ f (yoshidaEndpointA * x)) (Icc (-1) 1) :=
      f.property.1.continuousOn.comp (by fun_prop) hmap
    simpa only [w, Function.comp_apply] using
      Complex.continuous_re.comp_continuousOn hfOn
  let W : ℝ → ℝ := fun x ↦
    w (projIcc (-1) 1 (by norm_num) x)
  have hW_cont : Continuous W := by
    simpa only [W, Set.restrict_apply] using
      hwOn.restrict.comp continuous_projIcc
  have hW_eq (x : ℝ) (hx : x ∈ Icc (-1) 1) : W x = w x := by
    dsimp only [W]
    rw [projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) hx]
  have hrescale (y : ℝ)
      (hy : y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA) :
      W (y / yoshidaEndpointA) = (f y).re := by
    have hyScaled : y / yoshidaEndpointA ∈ Icc (-1) 1 := by
      constructor
      · rw [le_div_iff₀ yoshidaEndpointA_pos]
        simpa using hy.1
      · rw [div_le_iff₀ yoshidaEndpointA_pos]
        simpa using hy.2
    rw [hW_eq _ hyScaled]
    dsimp only [w]
    rw [show yoshidaEndpointA * (y / yoshidaEndpointA) = y by
      field_simp [yoshidaEndpointA_pos.ne']]
  have hpositive :
      yoshidaPositivePolarLinear yoshidaEndpointA yoshidaEndpointA_pos f =
        ((∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (-y / 2) * W (y / yoshidaEndpointA) : ℝ) : ℂ) := by
    rw [yoshidaPositivePolarLinear, yoshidaCenteredLaplaceLinear_apply,
      ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA := by
      simpa only [uIcc_of_le (by linarith [yoshidaEndpointA_pos] :
        -yoshidaEndpointA ≤ yoshidaEndpointA)] using hy
    change Complex.exp (-((1 / 2 : ℂ) * (y : ℂ))) * f y =
      ((Real.exp (-y / 2) * W (y / yoshidaEndpointA) : ℝ) : ℂ)
    rw [hf_real y hyIcc, hrescale y hyIcc]
    rw [show -((1 / 2 : ℂ) * (y : ℂ)) = ((-y / 2 : ℝ) : ℂ) by
      push_cast
      ring]
    rw [← Complex.ofReal_exp]
    push_cast
    rfl
  have hnegative :
      yoshidaNegativePolarLinear yoshidaEndpointA yoshidaEndpointA_pos f =
        ((∫ y : ℝ in -yoshidaEndpointA..yoshidaEndpointA,
          Real.exp (y / 2) * W (y / yoshidaEndpointA) : ℝ) : ℂ) := by
    rw [yoshidaNegativePolarLinear, yoshidaCenteredLaplaceLinear_apply,
      ← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro y hy
    have hyIcc : y ∈ Icc (-yoshidaEndpointA) yoshidaEndpointA := by
      simpa only [uIcc_of_le (by linarith [yoshidaEndpointA_pos] :
        -yoshidaEndpointA ≤ yoshidaEndpointA)] using hy
    change Complex.exp (-((-1 / 2 : ℂ) * (y : ℂ))) * f y =
      ((Real.exp (y / 2) * W (y / yoshidaEndpointA) : ℝ) : ℂ)
    rw [hf_real y hyIcc, hrescale y hyIcc]
    rw [show -((-1 / 2 : ℂ) * (y : ℂ)) = ((y / 2 : ℝ) : ℂ) by
      push_cast
      ring]
    rw [← Complex.ofReal_exp]
    push_cast
    rfl
  have hcosh :
      (∫ x : ℝ in -1..1,
          (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (W x : ℂ)) =
        ∫ x : ℝ in -1..1,
          (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (W x : ℂ) =
      (Real.cosh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)
    rw [hW_eq x (by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)]
  have hsinh :
      (∫ x : ℝ in -1..1,
          (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (W x : ℂ)) =
        ∫ x : ℝ in -1..1,
          (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    change (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (W x : ℂ) =
      (Real.sinh (yoshidaEndpointA * x / 2) : ℂ) * (w x : ℂ)
    rw [hW_eq x (by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx)]
  have hquadratic :
      yoshidaEndpointHyperbolicQuadratic (fun x ↦ (W x : ℂ)) =
        yoshidaEndpointHyperbolicQuadratic (fun x ↦ (w x : ℂ)) := by
    unfold yoshidaEndpointHyperbolicQuadratic
    rw [hcosh, hsinh]
  have hscale :=
    two_mul_rescaledPolarMoments_eq_endpointHyperbolicQuadratic W hW_cont
  rw [hquadratic] at hscale
  unfold clippedPolarEnergy
  rw [hpositive, hnegative]
  rw [Complex.star_def, Complex.conj_ofReal]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  simpa only [w, mul_assoc] using hscale

end

end ArithmeticHodge.Analysis.YoshidaEndpointClippedPolarBridge
