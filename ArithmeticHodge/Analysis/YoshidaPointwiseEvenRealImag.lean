import ArithmeticHodge.Analysis.YoshidaPointwiseOddRealImag
import ArithmeticHodge.Analysis.YoshidaPointwiseParityCore

set_option autoImplicit false

open Complex

namespace ArithmeticHodge.Analysis.YoshidaPointwiseEvenRealImag

open ArithmeticHodge.Analysis
open YoshidaPointwiseOddRealImag
open YoshidaPointwiseParityCore

noncomputable section

/-!
# Real and imaginary coefficients of the pointwise-even periodic carrier

The generic periodic-core coefficient projections preserve literal evenness.
This is the carrier-level input needed to reduce a complex even production
diagonal to two real even diagonals.
-/

/-- Real coefficient preserves literal pointwise evenness. -/
def pointwiseEvenPeriodicCoreRealPart {a : ℝ}
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) :
    yoshidaPointwiseEvenPeriodicCoreSubmodule a :=
  ⟨periodicCoreRealPart f.1, by
    intro x
    change ((((f.1 : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) (-x)).re : ℂ) =
      ((((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) x).re : ℂ)
    rw [f.property x]⟩

/-- Imaginary coefficient preserves literal pointwise evenness. -/
def pointwiseEvenPeriodicCoreImagPart {a : ℝ}
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) :
    yoshidaPointwiseEvenPeriodicCoreSubmodule a :=
  ⟨periodicCoreImagPart f.1, by
    intro x
    change ((((f.1 : YoshidaClippedPeriodicCore a) :
      YoshidaClippedSmooth a) (-x)).im : ℂ) =
      ((((f.1 : YoshidaClippedPeriodicCore a) :
        YoshidaClippedSmooth a) x).im : ℂ)
    rw [f.property x]⟩

theorem pointwiseEvenPeriodicCoreRealPart_im_zero {a x : ℝ}
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) :
    ((((pointwiseEvenPeriodicCoreRealPart f).1 :
      YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) x).im = 0 := by
  simp [pointwiseEvenPeriodicCoreRealPart]

theorem pointwiseEvenPeriodicCoreImagPart_im_zero {a x : ℝ}
    (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) :
    ((((pointwiseEvenPeriodicCoreImagPart f).1 :
      YoshidaClippedPeriodicCore a) : YoshidaClippedSmooth a) x).im = 0 := by
  simp [pointwiseEvenPeriodicCoreImagPart]

/-- Exact reconstruction in the structural even periodic carrier. -/
theorem pointwiseEvenPeriodicCoreRealPart_add_I_smul_imagPart
    {a : ℝ} (f : yoshidaPointwiseEvenPeriodicCoreSubmodule a) :
    pointwiseEvenPeriodicCoreRealPart f +
        Complex.I • pointwiseEvenPeriodicCoreImagPart f = f := by
  ext x
  apply Complex.ext
  · simp [pointwiseEvenPeriodicCoreRealPart,
      pointwiseEvenPeriodicCoreImagPart, periodicCoreRealPart,
      periodicCoreImagPart]
  · simp [pointwiseEvenPeriodicCoreRealPart,
      pointwiseEvenPeriodicCoreImagPart, periodicCoreRealPart,
      periodicCoreImagPart]

end

end ArithmeticHodge.Analysis.YoshidaPointwiseEvenRealImag
