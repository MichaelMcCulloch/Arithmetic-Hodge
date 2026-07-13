import ArithmeticHodge.Analysis.YoshidaClippedRealImag
import ArithmeticHodge.Analysis.YoshidaClippedEndpointContinuous
import Mathlib.Analysis.Calculus.ContDiff.RCLike

set_option autoImplicit false

open Complex Real Set
open scoped ContDiff

namespace ArithmeticHodge.Analysis.YoshidaPointwiseOddRealImag

open ArithmeticHodge.Analysis
open YoshidaClippedRealImag
open YoshidaClippedEndpointContinuous
open YoshidaPointwiseOddPeriodicCore

noncomputable section

/-- Taking the real coefficient preserves the periodic smooth source core. -/
theorem clippedRealPart_mem_periodicCore {a : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    clippedRealPart (f : YoshidaClippedSmooth a) ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  rcases f.property with ⟨F, hFdiff, hFperiodic, hFeq⟩
  refine ⟨fun x ↦ ((F x).re : ℂ), ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp
      (Complex.reCLM.contDiff.comp hFdiff)
  · intro x
    change ((F (x + 2 * a)).re : ℂ) = ((F x).re : ℂ)
    rw [hFperiodic]
  · intro x hx
    change ((F x).re : ℂ) = (((f : YoshidaClippedSmooth a) x).re : ℂ)
    rw [hFeq hx]

/-- Taking the imaginary coefficient preserves the periodic smooth source
core. -/
theorem clippedImagPart_mem_periodicCore {a : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    clippedImagPart (f : YoshidaClippedSmooth a) ∈
      yoshidaClippedPeriodicCoreSubmodule a := by
  rcases f.property with ⟨F, hFdiff, hFperiodic, hFeq⟩
  refine ⟨fun x ↦ ((F x).im : ℂ), ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp
      (Complex.imCLM.contDiff.comp hFdiff)
  · intro x
    change ((F (x + 2 * a)).im : ℂ) = ((F x).im : ℂ)
    rw [hFperiodic]
  · intro x hx
    change ((F x).im : ℂ) = (((f : YoshidaClippedSmooth a) x).im : ℂ)
    rw [hFeq hx]

/-- Real coefficient as an element of the periodic core. -/
def periodicCoreRealPart {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    YoshidaClippedPeriodicCore a :=
  ⟨clippedRealPart (f : YoshidaClippedSmooth a),
    clippedRealPart_mem_periodicCore f⟩

/-- Imaginary coefficient as an element of the periodic core. -/
def periodicCoreImagPart {a : ℝ} (f : YoshidaClippedPeriodicCore a) :
    YoshidaClippedPeriodicCore a :=
  ⟨clippedImagPart (f : YoshidaClippedSmooth a),
    clippedImagPart_mem_periodicCore f⟩

@[simp] theorem periodicCoreRealPart_apply {a x : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    (((periodicCoreRealPart f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) : ℝ → ℂ) x =
      ((((f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) x).re : ℂ) := rfl

@[simp] theorem periodicCoreImagPart_apply {a x : ℝ}
    (f : YoshidaClippedPeriodicCore a) :
    (((periodicCoreImagPart f : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) : ℝ → ℂ) x =
      ((((f : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) x).im : ℂ) := rfl

/-- Real coefficient preserves literal pointwise oddness. -/
def pointwiseOddPeriodicCoreRealPart {a : ℝ}
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    yoshidaPointwiseOddPeriodicCoreSubmodule a :=
  ⟨periodicCoreRealPart f.1, by
    intro x
    change ((((f.1 : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) (-x)).re : ℂ) =
      -((((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) x).re : ℂ)
    rw [f.property x]
    simp⟩

/-- Imaginary coefficient preserves literal pointwise oddness. -/
def pointwiseOddPeriodicCoreImagPart {a : ℝ}
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    yoshidaPointwiseOddPeriodicCoreSubmodule a :=
  ⟨periodicCoreImagPart f.1, by
    intro x
    change ((((f.1 : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) (-x)).im : ℂ) =
      -((((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) x).im : ℂ)
    rw [f.property x]
    simp⟩

theorem pointwiseOddPeriodicCoreRealPart_im_zero {a x : ℝ}
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    ((((pointwiseOddPeriodicCoreRealPart f).1 :
      YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) x).im = 0 := by
  simp [pointwiseOddPeriodicCoreRealPart]

theorem pointwiseOddPeriodicCoreImagPart_im_zero {a x : ℝ}
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    ((((pointwiseOddPeriodicCoreImagPart f).1 :
      YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) x).im = 0 := by
  simp [pointwiseOddPeriodicCoreImagPart]

/-- Exact real/imaginary reconstruction in the structural odd periodic
carrier. -/
theorem pointwiseOddPeriodicCoreRealPart_add_I_smul_imagPart
    {a : ℝ} (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    pointwiseOddPeriodicCoreRealPart f +
        Complex.I • pointwiseOddPeriodicCoreImagPart f = f := by
  ext x
  apply Complex.ext
  · simp [pointwiseOddPeriodicCoreRealPart,
      pointwiseOddPeriodicCoreImagPart, periodicCoreRealPart,
      periodicCoreImagPart]
  · simp [pointwiseOddPeriodicCoreRealPart,
      pointwiseOddPeriodicCoreImagPart, periodicCoreRealPart,
      periodicCoreImagPart]

/-- Real coefficient of a structural odd periodic source profile. -/
def pointwiseOddPeriodicCoreRealProfile {a : ℝ}
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) : ℝ → ℝ :=
  fun x ↦ ((((f.1 : YoshidaClippedPeriodicCore a) :
    YoshidaClippedSmooth a) : ℝ → ℂ) x).re

/-- Imaginary coefficient of a structural odd periodic source profile. -/
def pointwiseOddPeriodicCoreImagProfile {a : ℝ}
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) : ℝ → ℝ :=
  fun x ↦ ((((f.1 : YoshidaClippedPeriodicCore a) :
    YoshidaClippedSmooth a) : ℝ → ℂ) x).im

theorem pointwiseOddPeriodicCoreRealProfile_odd {a : ℝ}
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    Function.Odd (pointwiseOddPeriodicCoreRealProfile f) := by
  intro x
  change (((((f.1 : YoshidaClippedPeriodicCore a) :
    YoshidaClippedSmooth a) : ℝ → ℂ) (-x)).re) =
      -(((((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ) x).re)
  rw [f.property x]
  simp

theorem pointwiseOddPeriodicCoreImagProfile_odd {a : ℝ}
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    Function.Odd (pointwiseOddPeriodicCoreImagProfile f) := by
  intro x
  change (((((f.1 : YoshidaClippedPeriodicCore a) :
    YoshidaClippedSmooth a) : ℝ → ℂ) (-x)).im) =
      -(((((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ) x).im)
  rw [f.property x]
  simp

theorem continuous_pointwiseOddPeriodicCoreRealProfile
    {a : ℝ} (ha : 0 < a)
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    Continuous (pointwiseOddPeriodicCoreRealProfile f) := by
  have hends := pointwiseOddPeriodicCore_endpoints_zero ha f
  have hcontinuous : Continuous
      ((((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ)) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero ha _ hends.2 hends.1
  exact Complex.continuous_re.comp hcontinuous

theorem continuous_pointwiseOddPeriodicCoreImagProfile
    {a : ℝ} (ha : 0 < a)
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    Continuous (pointwiseOddPeriodicCoreImagProfile f) := by
  have hends := pointwiseOddPeriodicCore_endpoints_zero ha f
  have hcontinuous : Continuous
      ((((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) : ℝ → ℂ)) :=
    continuous_yoshidaClippedSmooth_of_endpoints_zero ha _ hends.2 hends.1
  exact Complex.continuous_im.comp hcontinuous

theorem locallyLipschitzOn_centered_pointwiseOddPeriodicCoreRealProfile
    {a : ℝ} (ha : 0 < a)
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    LocallyLipschitzOn (Icc (-1) 1)
      (fun x ↦ pointwiseOddPeriodicCoreRealProfile f (a * x)) := by
  have hprofile : ContDiffOn ℝ 1
      (pointwiseOddPeriodicCoreRealProfile f) (Icc (-a) a) := by
    exact Complex.reCLM.contDiff.comp_contDiffOn
      (((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a).property.1.of_le (by simp))
  have hscale : ContDiffOn ℝ 1 (fun x : ℝ ↦ a * x) (Icc (-1) 1) := by
    fun_prop
  have hmaps : MapsTo (fun x : ℝ ↦ a * x)
      (Icc (-1) 1) (Icc (-a) a) := by
    intro x hx
    constructor <;> nlinarith [hx.1, hx.2]
  have hcomp := hprofile.comp hscale hmaps
  simpa only [Function.comp_apply] using
    hcomp.locallyLipschitzOn (convex_Icc (-1) 1)

theorem locallyLipschitzOn_centered_pointwiseOddPeriodicCoreImagProfile
    {a : ℝ} (ha : 0 < a)
    (f : yoshidaPointwiseOddPeriodicCoreSubmodule a) :
    LocallyLipschitzOn (Icc (-1) 1)
      (fun x ↦ pointwiseOddPeriodicCoreImagProfile f (a * x)) := by
  have hprofile : ContDiffOn ℝ 1
      (pointwiseOddPeriodicCoreImagProfile f) (Icc (-a) a) := by
    exact Complex.imCLM.contDiff.comp_contDiffOn
      (((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a).property.1.of_le (by simp))
  have hscale : ContDiffOn ℝ 1 (fun x : ℝ ↦ a * x) (Icc (-1) 1) := by
    fun_prop
  have hmaps : MapsTo (fun x : ℝ ↦ a * x)
      (Icc (-1) 1) (Icc (-a) a) := by
    intro x hx
    constructor <;> nlinarith [hx.1, hx.2]
  have hcomp := hprofile.comp hscale hmaps
  simpa only [Function.comp_apply] using
    hcomp.locallyLipschitzOn (convex_Icc (-1) 1)

end

end ArithmeticHodge.Analysis.YoshidaPointwiseOddRealImag
