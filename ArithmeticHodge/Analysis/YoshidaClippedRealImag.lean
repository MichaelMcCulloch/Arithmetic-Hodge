import ArithmeticHodge.Analysis.YoshidaPointwiseOddPeriodicCore
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false

open Complex Real Set

namespace ArithmeticHodge.Analysis.YoshidaClippedRealImag

open ArithmeticHodge.Analysis
open YoshidaPointwiseOddPeriodicCore

noncomputable section

/-- The real-valued clipped component, retained in the complex carrier. -/
def clippedRealPart {a : ℝ} (f : YoshidaClippedSmooth a) :
    YoshidaClippedSmooth a :=
  ⟨fun x ↦ ((f x).re : ℂ), by
    constructor
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
        (Complex.reCLM.contDiff.comp_contDiffOn f.property.1)
    · intro x hx
      change ((f x).re : ℂ) = 0
      rw [yoshidaClippedSmooth_eq_zero_outside f hx]
      norm_num⟩

/-- The imaginary coefficient as a real-valued clipped component. -/
def clippedImagPart {a : ℝ} (f : YoshidaClippedSmooth a) :
    YoshidaClippedSmooth a :=
  ⟨fun x ↦ ((f x).im : ℂ), by
    constructor
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
        (Complex.imCLM.contDiff.comp_contDiffOn f.property.1)
    · intro x hx
      change ((f x).im : ℂ) = 0
      rw [yoshidaClippedSmooth_eq_zero_outside f hx]
      norm_num⟩

@[simp] theorem clippedRealPart_apply {a x : ℝ}
    (f : YoshidaClippedSmooth a) :
    clippedRealPart f x = ((f x).re : ℂ) := rfl

@[simp] theorem clippedImagPart_apply {a x : ℝ}
    (f : YoshidaClippedSmooth a) :
    clippedImagPart f x = ((f x).im : ℂ) := rfl

/-- Exact real/imaginary reconstruction inside the clipped carrier. -/
theorem clippedRealPart_add_I_smul_imagPart
    {a : ℝ} (f : YoshidaClippedSmooth a) :
    clippedRealPart f + Complex.I • clippedImagPart f = f := by
  ext x
  apply Complex.ext
  · simp [clippedRealPart, clippedImagPart]
  · simp [clippedRealPart, clippedImagPart]

end

end ArithmeticHodge.Analysis.YoshidaClippedRealImag
